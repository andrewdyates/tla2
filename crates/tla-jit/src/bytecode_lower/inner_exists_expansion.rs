// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Inner EXISTS pre-expansion for JIT compilation.
//!
//! When a next-state action contains inner `ExistsBegin` quantifiers with
//! statically-known domains, this module expands the action into multiple
//! specialized functions -- one per binding combination. Each specialized
//! function has the EXISTS loop removed and replaced with a concrete `LoadImm`
//! constant for the binding variable.
//!
//! # Example
//!
//! ```text
//! SendMsg(sender) ==
//!   \E receiver \in Nodes \ {sender} :
//!     msg' = msg @@ (receiver :> sender)
//! ```
//!
//! With `Nodes = {0, 1, 2}` and `sender = 0`, the inner EXISTS over
//! `{1, 2}` is expanded into two functions:
//!
//! - `SendMsg__0__1`: receiver=1, EXISTS loop removed
//! - `SendMsg__0__2`: receiver=2, EXISTS loop removed
//!
//! Each produces a single successor, compatible with the JIT ABI.
//!
//! # Limitations (Phase 1)
//!
//! - Only handles EXISTS domains that can be statically determined from the
//!   bytecode's constant pool (integer ranges, enumerated sets, model values).
//! - Domain size capped at `MAX_INNER_DOMAIN_SIZE` (100) to prevent
//!   combinatorial explosion.
//! - State-dependent domains (e.g., filtering by state variable values)
//!   remain on the interpreter path (Phase 2).
//!
//! Part of #4176: JIT EXISTS binding dispatch.

use tla_tir::bytecode::{BytecodeFunction, ConstantPool, Opcode};

/// Maximum domain size for inner EXISTS expansion. Actions with larger
/// domains stay on the interpreter path to avoid combinatorial explosion.
pub(crate) const MAX_INNER_DOMAIN_SIZE: usize = 100;

/// Maximum total expanded functions from a single base action.
/// Prevents combinatorial explosion: e.g., 3 nested EXISTS with domain
/// size 10 = 1000 functions. Cap at this limit.
const MAX_TOTAL_EXPANSIONS: usize = 500;

/// Describes a single inner EXISTS quantifier found in a bytecode function.
#[derive(Debug, Clone)]
pub(crate) struct InnerExistsInfo {
    /// PC of the ExistsBegin opcode.
    pub(crate) begin_pc: usize,
    /// PC of the matching ExistsNext opcode.
    pub(crate) next_pc: usize,
    /// The register that holds the binding variable (`r_binding`).
    pub(crate) r_binding: u8,
    /// The register that holds the domain set (`r_domain`).
    #[allow(dead_code)]
    pub(crate) r_domain: u8,
    /// The register for the result (`rd`).
    #[allow(dead_code)]
    pub(crate) rd: u8,
    /// The domain elements (if statically known).
    pub(crate) domain: Option<Vec<i64>>,
    /// The loop_end offset from ExistsBegin.
    #[allow(dead_code)]
    pub(crate) loop_end_offset: i32,
}

/// Analyze a bytecode function to find all inner EXISTS quantifiers.
///
/// Returns a list of `InnerExistsInfo` for each ExistsBegin in the function.
pub(crate) fn find_inner_exists(func: &BytecodeFunction) -> Vec<InnerExistsInfo> {
    let mut results = Vec::new();

    for (pc, op) in func.instructions.iter().enumerate() {
        if let Opcode::ExistsBegin {
            rd,
            r_binding,
            r_domain,
            loop_end,
        } = *op
        {
            // Find the matching ExistsNext by scanning forward.
            let target_pc = (pc as i64 + loop_end as i64) as usize;
            let mut next_pc = None;

            // The ExistsNext should be somewhere between begin_pc+1 and target_pc,
            // with a backward jump to the instruction after ExistsBegin.
            for scan_pc in (pc + 1)..func.instructions.len().min(target_pc + 1) {
                if let Opcode::ExistsNext { loop_begin, .. } = func.instructions[scan_pc] {
                    let jump_target = (scan_pc as i64 + loop_begin as i64) as usize;
                    if jump_target == pc + 1 {
                        next_pc = Some(scan_pc);
                        break;
                    }
                }
            }

            results.push(InnerExistsInfo {
                begin_pc: pc,
                next_pc: next_pc.unwrap_or(target_pc.saturating_sub(1)),
                r_binding,
                r_domain,
                rd,
                domain: None,
                loop_end_offset: loop_end,
            });
        }
    }

    results
}

/// Resolve the domain elements for each inner EXISTS in the function.
///
/// For each EXISTS, resolves its domain register using only instructions
/// BEFORE the ExistsBegin PC. This is critical because later instructions
/// (inside the loop body or after it) can overwrite registers used by
/// SetEnum elements.
///
/// For example:
/// ```text
///   LoadImm { rd: 4, value: 20 }  // PC 1
///   SetEnum { rd: 2, start: 3, count: 3 }  // PC 3 -- uses regs 3,4,5
///   ExistsBegin { r_domain: 2, ... }  // PC 4
///   LoadBool { rd: 4, value: true }  // PC 6 -- overwrites reg 4!
/// ```
///
/// If we scanned ALL instructions, reg 4 would resolve to 1 (true) instead
/// of 20. By scanning only the prefix, we get the correct value.
///
/// We do NOT delegate to `collect_quantifier_domains_from_bytecode` because
/// that function requires the Begin opcodes in the scanned slice (Step 2
/// iterates over Begin opcodes to find r_domain). Instead, we directly
/// resolve from SetEnum + register constants.
///
/// Part of #4176: JIT EXISTS binding dispatch.
pub(crate) fn resolve_inner_exists_domains(
    func: &BytecodeFunction,
    constants: Option<&ConstantPool>,
    exists_list: &mut [InnerExistsInfo],
) {
    use std::collections::HashMap;

    for info in exists_list.iter_mut() {
        // Only scan instructions up to (but not including) the ExistsBegin.
        // This ensures we see the register values as they were at the point
        // of the ExistsBegin, before the loop body can overwrite them.
        let prefix = &func.instructions[..info.begin_pc];

        // Build register constant map, set maps, and range maps from prefix only.
        let mut reg_constants: HashMap<u8, i64> = HashMap::new();
        let mut set_enum_map: HashMap<u8, (u8, u8)> = HashMap::new();
        // Resolved set elements per register (from SetEnum, Range, LoadConst, SetDiff).
        let mut reg_set_elements: HashMap<u8, Vec<i64>> = HashMap::new();
        // Range opcodes: rd => (r_lo, r_hi).
        let mut range_map: HashMap<u8, (u8, u8)> = HashMap::new();
        // SetDiff opcodes: rd => (r_left, r_right).
        let mut set_diff_map: HashMap<u8, (u8, u8)> = HashMap::new();

        for op in prefix {
            match *op {
                Opcode::LoadImm { rd, value } => {
                    reg_constants.insert(rd, value);
                }
                Opcode::LoadBool { rd, value } => {
                    reg_constants.insert(rd, if value { 1 } else { 0 });
                }
                Opcode::LoadConst { rd, idx } => {
                    if let Some(pool) = constants {
                        let val = pool.get_value(idx);
                        match val {
                            tla_value::Value::SmallInt(n) => {
                                reg_constants.insert(rd, *n);
                            }
                            tla_value::Value::Bool(b) => {
                                reg_constants.insert(rd, if *b { 1 } else { 0 });
                            }
                            tla_value::Value::String(s) => {
                                let name_id = tla_core::intern_name(s);
                                reg_constants.insert(rd, name_id.0 as i64);
                            }
                            tla_value::Value::ModelValue(s) => {
                                let name_id = tla_core::intern_name(s);
                                reg_constants.insert(rd, name_id.0 as i64);
                            }
                            // Phase 2: Handle set values from constant pool.
                            tla_value::Value::Set(set) => {
                                let mut elements = Vec::new();
                                let mut all_scalar = true;
                                for elem in set.iter() {
                                    match elem {
                                        tla_value::Value::SmallInt(n) => {
                                            elements.push(*n);
                                        }
                                        tla_value::Value::Bool(b) => {
                                            elements.push(if *b { 1 } else { 0 });
                                        }
                                        tla_value::Value::String(s) => {
                                            let name_id = tla_core::intern_name(s);
                                            elements.push(name_id.0 as i64);
                                        }
                                        tla_value::Value::ModelValue(s) => {
                                            let name_id = tla_core::intern_name(s);
                                            elements.push(name_id.0 as i64);
                                        }
                                        _ => {
                                            all_scalar = false;
                                            break;
                                        }
                                    }
                                }
                                if all_scalar && elements.len() <= MAX_INNER_DOMAIN_SIZE {
                                    reg_set_elements.insert(rd, elements);
                                }
                            }
                            tla_value::Value::Interval(iv) => {
                                use num_traits::ToPrimitive;
                                if let (Some(lo_val), Some(hi_val)) =
                                    (iv.low().to_i64(), iv.high().to_i64())
                                {
                                    if hi_val >= lo_val {
                                        let count = (hi_val - lo_val + 1) as usize;
                                        if count <= MAX_INNER_DOMAIN_SIZE {
                                            let elements: Vec<i64> =
                                                (lo_val..=hi_val).collect();
                                            reg_set_elements.insert(rd, elements);
                                        }
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
                Opcode::Move { rd, rs } => {
                    // Propagate known constants through Move instructions.
                    // After outer binding specialization, LoadImm { rd: 0, value: X }
                    // followed by Move { rd: N, rs: 0 } should transfer the constant.
                    if let Some(&val) = reg_constants.get(&rs) {
                        reg_constants.insert(rd, val);
                    }
                    // Also propagate resolved set elements (e.g., Move of a set register).
                    if let Some(elements) = reg_set_elements.get(&rs).cloned() {
                        reg_set_elements.insert(rd, elements);
                    }
                }
                Opcode::SetEnum { rd, start, count } => {
                    set_enum_map.insert(rd, (start, count));
                }
                Opcode::Range { rd, lo, hi } => {
                    range_map.insert(rd, (lo, hi));
                }
                Opcode::SetDiff { rd, r1, r2 } => {
                    set_diff_map.insert(rd, (r1, r2));
                }
                _ => {}
            }
        }

        // Resolve SetEnum elements into reg_set_elements.
        for (&rd, &(start, count)) in &set_enum_map {
            let mut elements = Vec::with_capacity(count as usize);
            let mut all_resolved = true;
            for i in 0..count {
                let elem_reg = start + i;
                if let Some(&val) = reg_constants.get(&elem_reg) {
                    elements.push(val);
                } else {
                    all_resolved = false;
                    break;
                }
            }
            if all_resolved {
                reg_set_elements.insert(rd, elements);
            }
        }

        // Resolve Range opcodes into reg_set_elements.
        for (&rd, &(r_lo, r_hi)) in &range_map {
            if let (Some(&lo), Some(&hi)) = (
                reg_constants.get(&r_lo),
                reg_constants.get(&r_hi),
            ) {
                if hi >= lo {
                    let count = (hi - lo + 1) as usize;
                    if count <= MAX_INNER_DOMAIN_SIZE {
                        let elements: Vec<i64> = (lo..=hi).collect();
                        reg_set_elements.insert(rd, elements);
                    }
                }
            }
        }

        // Resolve SetDiff opcodes: if both operands are known sets,
        // compute the difference. This handles patterns like `Node \ {i}`
        // after outer binding specialization where both Node and {i} are known.
        for (&rd, &(r1, r2)) in &set_diff_map {
            if let (Some(left), Some(right)) = (
                reg_set_elements.get(&r1),
                reg_set_elements.get(&r2),
            ) {
                let right_set: std::collections::HashSet<i64> =
                    right.iter().copied().collect();
                let diff: Vec<i64> = left
                    .iter()
                    .copied()
                    .filter(|v| !right_set.contains(v))
                    .collect();
                if diff.len() <= MAX_INNER_DOMAIN_SIZE {
                    reg_set_elements.insert(rd, diff);
                }
            }
        }

        // Resolve domain for r_domain from any resolved set.
        if let Some(elements) = reg_set_elements.get(&info.r_domain) {
            if elements.len() <= MAX_INNER_DOMAIN_SIZE {
                info.domain = Some(elements.clone());
            }
        }
    }
}

/// Check if a bytecode function has inner EXISTS that can be statically expanded.
///
/// Returns `true` if ALL inner EXISTS have known, small domains.
pub(crate) fn can_expand_inner_exists(
    func: &BytecodeFunction,
    constants: Option<&ConstantPool>,
) -> bool {
    let mut exists_list = find_inner_exists(func);
    if exists_list.is_empty() {
        return false;
    }

    resolve_inner_exists_domains(func, constants, &mut exists_list);

    // All EXISTS must have resolved domains for expansion to work
    let all_resolved = exists_list.iter().all(|info| info.domain.is_some());
    if !all_resolved {
        return false;
    }

    // Check total expansion count: product of all domain sizes
    let total: usize = exists_list
        .iter()
        .filter_map(|info| info.domain.as_ref().map(|d| d.len()))
        .product();

    total > 0 && total <= MAX_TOTAL_EXPANSIONS
}

/// Result of expanding a single inner EXISTS quantifier.
#[derive(Debug, Clone)]
pub(crate) struct ExpandedAction {
    /// The specialized bytecode function with the EXISTS removed.
    pub(crate) func: BytecodeFunction,
    /// The binding values used for this expansion (one per expanded EXISTS).
    pub(crate) inner_binding_values: Vec<i64>,
}

/// Expand inner EXISTS quantifiers by rewriting bytecode while preserving
/// instruction offsets.
///
/// For each combination of inner EXISTS binding values, produces a specialized
/// bytecode function where:
/// 1. Each `ExistsBegin` is replaced with `LoadImm { rd: r_binding, value }`
/// 2. Each `ExistsNext` is replaced with `Move { rd, rs: r_body }`
/// 3. Instruction count is preserved, so all jump offsets remain valid.
///
/// Returns `None` if the function cannot be expanded (domains unknown or too large).
///
/// Part of #4176: JIT EXISTS binding dispatch.
pub(crate) fn expand_inner_exists_preserving_offsets(
    func: &BytecodeFunction,
    constants: Option<&ConstantPool>,
) -> Option<Vec<ExpandedAction>> {
    let mut exists_list = find_inner_exists(func);
    if exists_list.is_empty() {
        return None;
    }

    resolve_inner_exists_domains(func, constants, &mut exists_list);

    // For Phase 1, only handle the case where ALL inner EXISTS can be expanded
    if !exists_list.iter().all(|info| info.domain.is_some()) {
        return None;
    }

    // Check total expansion count
    let total: usize = exists_list
        .iter()
        .filter_map(|info| info.domain.as_ref().map(|d| d.len()))
        .product();

    if total == 0 || total > MAX_TOTAL_EXPANSIONS {
        return None;
    }

    // Generate all binding combinations using cartesian product
    let domains: Vec<&Vec<i64>> = exists_list
        .iter()
        .filter_map(|info| info.domain.as_ref())
        .collect();

    let combinations = cartesian_product(&domains);

    let mut expanded = Vec::with_capacity(combinations.len());

    for combo in &combinations {
        let specialized = rewrite_function_with_bindings(func, &exists_list, combo);
        expanded.push(ExpandedAction {
            func: specialized,
            inner_binding_values: combo.clone(),
        });
    }

    Some(expanded)
}

/// Compute the cartesian product of multiple domain vectors.
fn cartesian_product(domains: &[&Vec<i64>]) -> Vec<Vec<i64>> {
    if domains.is_empty() {
        return vec![Vec::new()];
    }

    let mut result = vec![Vec::new()];

    for domain in domains {
        let mut new_result = Vec::with_capacity(result.len() * domain.len());
        for existing in &result {
            for &val in *domain {
                let mut combo = existing.clone();
                combo.push(val);
                new_result.push(combo);
            }
        }
        result = new_result;
    }

    result
}

/// Rewrite a bytecode function, replacing each inner EXISTS with a concrete
/// binding value. The instruction count is preserved by replacing EXISTS
/// opcodes 1-to-1 with equivalent non-loop opcodes.
///
/// For each EXISTS at index `i`, `binding_values[i]` is used.
///
/// Replacement rules:
/// - `ExistsBegin { rd, r_binding, r_domain, loop_end }` ->
///   `LoadImm { rd: r_binding, value: binding_values[i] }`
///   (loads the concrete binding value into the binding register)
///
/// - `ExistsNext { rd, r_binding, r_body, loop_begin }` ->
///   `Move { rd, rs: r_body }`
///   (the EXISTS result is just the body result for this single binding;
///   semantically: rd = false OR r_body = r_body)
fn rewrite_function_with_bindings(
    func: &BytecodeFunction,
    exists_list: &[InnerExistsInfo],
    binding_values: &[i64],
) -> BytecodeFunction {
    let mut new_instructions = func.instructions.clone();

    for (idx, info) in exists_list.iter().enumerate() {
        let binding_value = binding_values[idx];

        // Replace ExistsBegin with LoadImm for binding register
        new_instructions[info.begin_pc] = Opcode::LoadImm {
            rd: info.r_binding,
            value: binding_value,
        };

        // Replace ExistsNext with Move rd <- r_body
        // Original semantics: rd = rd OR r_body (across iterations).
        // With a single binding: rd = false OR r_body = r_body.
        if let Opcode::ExistsNext { rd, r_body, .. } = new_instructions[info.next_pc] {
            new_instructions[info.next_pc] = Opcode::Move { rd, rs: r_body };
        }
    }

    let mut new_func = BytecodeFunction::new(func.name.clone(), func.max_register);
    for op in new_instructions {
        new_func.emit(op);
    }

    new_func
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a simple function with an inner EXISTS:
    /// \E x \in {1, 2, 3} : x > input
    fn make_exists_function() -> (BytecodeFunction, tla_tir::bytecode::ConstantPool) {
        let mut func = BytecodeFunction::new("TestExists".to_string(), 5);
        let pool = tla_tir::bytecode::ConstantPool::new();

        // Register layout:
        // r0 = result (rd)
        // r1 = binding (x)
        // r2 = domain set
        // r3, r4, r5 = domain elements / temporaries

        // Load domain elements into registers for SetEnum
        func.emit(Opcode::LoadImm { rd: 3, value: 1 }); // PC 0
        func.emit(Opcode::LoadImm { rd: 4, value: 2 }); // PC 1
        func.emit(Opcode::LoadImm { rd: 5, value: 3 }); // PC 2
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 3,
            count: 3,
        }); // PC 3

        // ExistsBegin: \E x(r1) \in r2 : body
        func.emit(Opcode::ExistsBegin {
            rd: 0,
            r_binding: 1,
            r_domain: 2,
            loop_end: 4, // jump to PC 8 (4+4)
        }); // PC 4

        // Body: r4 = r1 > r3 (x > input)
        func.emit(Opcode::LoadVar { rd: 3, var_idx: 0 }); // PC 5
        func.emit(Opcode::GtInt {
            rd: 4,
            r1: 1,
            r2: 3,
        }); // PC 6

        // ExistsNext
        func.emit(Opcode::ExistsNext {
            rd: 0,
            r_binding: 1,
            r_body: 4,
            loop_begin: -2, // jump back to PC 5
        }); // PC 7

        // Return result
        func.emit(Opcode::Ret { rs: 0 }); // PC 8

        (func, pool)
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_find_inner_exists_basic() {
        let (func, _pool) = make_exists_function();
        let exists = find_inner_exists(&func);

        assert_eq!(exists.len(), 1, "should find one inner EXISTS");
        assert_eq!(exists[0].begin_pc, 4);
        assert_eq!(exists[0].next_pc, 7);
        assert_eq!(exists[0].r_binding, 1);
        assert_eq!(exists[0].r_domain, 2);
        assert_eq!(exists[0].rd, 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_resolve_domains() {
        let (func, pool) = make_exists_function();
        let mut exists = find_inner_exists(&func);
        resolve_inner_exists_domains(&func, Some(&pool), &mut exists);

        assert_eq!(exists.len(), 1);
        // The domain should be {1, 2, 3} from the SetEnum
        let domain = exists[0].domain.as_ref().expect("domain should be resolved");
        assert_eq!(domain, &[1, 2, 3]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_can_expand_basic() {
        let (func, pool) = make_exists_function();
        assert!(
            can_expand_inner_exists(&func, Some(&pool)),
            "should be expandable with small constant domain"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_expand_preserving_offsets() {
        let (func, pool) = make_exists_function();
        let expanded =
            expand_inner_exists_preserving_offsets(&func, Some(&pool)).expect("should expand");

        assert_eq!(expanded.len(), 3, "3 elements in domain = 3 expansions");

        // Check binding values
        assert_eq!(expanded[0].inner_binding_values, vec![1]);
        assert_eq!(expanded[1].inner_binding_values, vec![2]);
        assert_eq!(expanded[2].inner_binding_values, vec![3]);

        // Check that ExistsBegin is replaced with LoadImm
        for (i, expansion) in expanded.iter().enumerate() {
            let expected_value = (i + 1) as i64;
            match expansion.func.instructions[4] {
                Opcode::LoadImm { rd, value } => {
                    assert_eq!(rd, 1, "should load into binding register");
                    assert_eq!(value, expected_value, "should have correct binding value");
                }
                ref other => panic!(
                    "expected LoadImm at PC 4, got {:?} for expansion {}",
                    other, i
                ),
            }

            // Check that ExistsNext is replaced with Move
            match expansion.func.instructions[7] {
                Opcode::Move { rd, rs } => {
                    assert_eq!(rd, 0, "should move to result register");
                    assert_eq!(rs, 4, "should move from body result register");
                }
                ref other => panic!(
                    "expected Move at PC 7, got {:?} for expansion {}",
                    other, i
                ),
            }

            // Instruction count should be preserved
            assert_eq!(
                expansion.func.instructions.len(),
                func.instructions.len(),
                "instruction count must be preserved"
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_expand_no_exists_returns_none() {
        // Function without EXISTS
        let mut func = BytecodeFunction::new("NoExists".to_string(), 2);
        func.emit(Opcode::LoadImm { rd: 0, value: 42 });
        func.emit(Opcode::Ret { rs: 0 });

        let pool = tla_tir::bytecode::ConstantPool::new();
        let result = expand_inner_exists_preserving_offsets(&func, Some(&pool));
        assert!(result.is_none(), "function without EXISTS should return None");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cartesian_product_empty() {
        let result = cartesian_product(&[]);
        assert_eq!(result, vec![Vec::<i64>::new()]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cartesian_product_single() {
        let d1 = vec![1, 2, 3];
        let result = cartesian_product(&[&d1]);
        assert_eq!(result, vec![vec![1], vec![2], vec![3]]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cartesian_product_two() {
        let d1 = vec![1, 2];
        let d2 = vec![10, 20];
        let result = cartesian_product(&[&d1, &d2]);
        assert_eq!(
            result,
            vec![vec![1, 10], vec![1, 20], vec![2, 10], vec![2, 20]]
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_can_expand_rejects_unresolvable_domain() {
        let mut func = BytecodeFunction::new("UnresolvableDomain".to_string(), 5);
        let pool = tla_tir::bytecode::ConstantPool::new();

        // EXISTS with a domain register that has no known constant source
        func.emit(Opcode::ExistsBegin {
            rd: 0,
            r_binding: 1,
            r_domain: 2,
            loop_end: 2,
        });
        func.emit(Opcode::ExistsNext {
            rd: 0,
            r_binding: 1,
            r_body: 3,
            loop_begin: -1,
        });
        func.emit(Opcode::Ret { rs: 0 });

        assert!(
            !can_expand_inner_exists(&func, Some(&pool)),
            "should not expand when domain cannot be resolved"
        );
    }

    /// Build a function with a next-state EXISTS pattern:
    /// \E receiver \in {0, 1, 2} : state_out[0] = receiver
    fn make_next_state_exists_function() -> (BytecodeFunction, tla_tir::bytecode::ConstantPool) {
        let mut func = BytecodeFunction::new("SendMsg".to_string(), 5);
        let pool = tla_tir::bytecode::ConstantPool::new();

        // Load domain elements
        func.emit(Opcode::LoadImm { rd: 3, value: 0 }); // PC 0
        func.emit(Opcode::LoadImm { rd: 4, value: 1 }); // PC 1
        func.emit(Opcode::LoadImm { rd: 5, value: 2 }); // PC 2
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 3,
            count: 3,
        }); // PC 3

        // ExistsBegin: \E receiver(r1) \in r2
        func.emit(Opcode::ExistsBegin {
            rd: 0,
            r_binding: 1,
            r_domain: 2,
            loop_end: 4, // -> PC 8
        }); // PC 4

        // Body: store receiver to state var 0
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 1 }); // PC 5
        func.emit(Opcode::LoadBool { rd: 4, value: true }); // PC 6

        // ExistsNext
        func.emit(Opcode::ExistsNext {
            rd: 0,
            r_binding: 1,
            r_body: 4,
            loop_begin: -2, // -> PC 5
        }); // PC 7

        func.emit(Opcode::Ret { rs: 0 }); // PC 8

        (func, pool)
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_expand_next_state_action() {
        let (func, pool) = make_next_state_exists_function();
        let expanded =
            expand_inner_exists_preserving_offsets(&func, Some(&pool)).expect("should expand");

        assert_eq!(expanded.len(), 3);

        for (i, expansion) in expanded.iter().enumerate() {
            let expected_value = i as i64;

            // PC 4: should be LoadImm for binding
            match expansion.func.instructions[4] {
                Opcode::LoadImm { rd, value } => {
                    assert_eq!(rd, 1);
                    assert_eq!(value, expected_value);
                }
                ref other => panic!("expected LoadImm, got {:?}", other),
            }

            // PC 5: should still be StoreVar (body preserved)
            assert!(
                matches!(
                    expansion.func.instructions[5],
                    Opcode::StoreVar { var_idx: 0, rs: 1 }
                ),
                "body instruction should be preserved"
            );

            // PC 7: ExistsNext replaced with Move
            assert!(
                matches!(expansion.func.instructions[7], Opcode::Move { rd: 0, rs: 4 }),
                "ExistsNext should be replaced with Move"
            );

            // No ExistsBegin or ExistsNext should remain
            for (pc, op) in expansion.func.instructions.iter().enumerate() {
                assert!(
                    !matches!(op, Opcode::ExistsBegin { .. }),
                    "ExistsBegin should not remain at PC {pc}"
                );
                assert!(
                    !matches!(op, Opcode::ExistsNext { .. }),
                    "ExistsNext should not remain at PC {pc}"
                );
            }
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_expanded_functions_have_no_exists_opcodes() {
        let (func, pool) = make_exists_function();
        let expanded =
            expand_inner_exists_preserving_offsets(&func, Some(&pool)).expect("should expand");

        for expansion in &expanded {
            for (pc, op) in expansion.func.instructions.iter().enumerate() {
                assert!(
                    !matches!(op, Opcode::ExistsBegin { .. } | Opcode::ExistsNext { .. }),
                    "EXISTS opcode should not remain at PC {pc}: {:?}",
                    op,
                );
            }
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cartesian_product_three() {
        let d1 = vec![1, 2];
        let d2 = vec![10];
        let d3 = vec![100, 200];
        let result = cartesian_product(&[&d1, &d2, &d3]);
        assert_eq!(
            result,
            vec![
                vec![1, 10, 100],
                vec![1, 10, 200],
                vec![2, 10, 100],
                vec![2, 10, 200],
            ]
        );
    }

    /// Test the exact bytecode pattern from EWD998 `SendMsg(sender)`:
    /// After outer binding specialization with sender=0, the inner EXISTS
    /// domain `Node \ {sender}` is computed via:
    ///   LoadImm { rd: 0, value: 0 }   -- prepended by specialization
    ///   ...
    ///   LoadConst { rd: 12, idx: 0 }  -- loads Node = {0, 1, 2}
    ///   Move { rd: 13, rs: 0 }        -- copies sender to temp reg
    ///   SetEnum { rd: 14, start: 13, count: 1 }  -- builds {sender}
    ///   SetDiff { rd: 15, r1: 12, r2: 14 }  -- Node \ {sender}
    ///   ExistsBegin { r_domain: 15, ... }
    ///
    /// This tests that `Move` propagation enables `SetEnum` + `SetDiff`
    /// domain resolution.
    ///
    /// Part of #4176: JIT EXISTS binding dispatch.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_resolve_domain_with_move_and_set_diff() {
        use tla_value::Value;

        let mut func = BytecodeFunction::new("SendMsg__0_0".to_string(), 20);
        let mut pool = tla_tir::bytecode::ConstantPool::new();

        // Prepended by outer specialization: sender = 0
        func.emit(Opcode::LoadImm { rd: 0, value: 0 }); // PC 0

        // Original function body (shifted by 1):
        // Load Node = {0, 1, 2} from constant pool
        let node_set = Value::set(vec![
            Value::SmallInt(0),
            Value::SmallInt(1),
            Value::SmallInt(2),
        ]);
        let node_idx = pool.add_value(node_set);
        func.emit(Opcode::LoadConst { rd: 12, idx: node_idx }); // PC 1

        // Move sender (reg 0) to temp reg 13
        func.emit(Opcode::Move { rd: 13, rs: 0 }); // PC 2

        // Build singleton set {sender} = {0}
        func.emit(Opcode::SetEnum { rd: 14, start: 13, count: 1 }); // PC 3

        // SetDiff: Node \ {sender} = {1, 2}
        func.emit(Opcode::SetDiff { rd: 15, r1: 12, r2: 14 }); // PC 4

        // ExistsBegin over the difference set
        func.emit(Opcode::ExistsBegin {
            rd: 16,
            r_binding: 17,
            r_domain: 15,
            loop_end: 4, // -> PC 9
        }); // PC 5

        // Body: store binding to state var
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 17 }); // PC 6
        func.emit(Opcode::LoadBool { rd: 18, value: true }); // PC 7

        // ExistsNext
        func.emit(Opcode::ExistsNext {
            rd: 16,
            r_binding: 17,
            r_body: 18,
            loop_begin: -2, // -> PC 6
        }); // PC 8

        func.emit(Opcode::Ret { rs: 16 }); // PC 9

        // Verify domain resolves to {1, 2} (Node \ {0})
        assert!(
            can_expand_inner_exists(&func, Some(&pool)),
            "should expand: Move propagates sender=0 through SetEnum to SetDiff"
        );

        let expanded = expand_inner_exists_preserving_offsets(&func, Some(&pool))
            .expect("expansion should succeed");
        assert_eq!(expanded.len(), 2, "Node \\ {{0}} = {{1, 2}} -> 2 expansions");

        let mut binding_values: Vec<i64> = expanded
            .iter()
            .map(|e| e.inner_binding_values[0])
            .collect();
        binding_values.sort();
        assert_eq!(binding_values, vec![1, 2], "binding values should be {{1, 2}}");

        // Verify no EXISTS opcodes remain
        for expansion in &expanded {
            for (pc, op) in expansion.func.instructions.iter().enumerate() {
                assert!(
                    !matches!(op, Opcode::ExistsBegin { .. } | Opcode::ExistsNext { .. }),
                    "EXISTS opcode should not remain at PC {pc}: {:?}",
                    op,
                );
            }
        }
    }
}
