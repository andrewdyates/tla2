// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Gate rewriting after equivalence merges.
//!
//! When two literals are merged (discovered equivalent), all gates
//! containing either literal must be rewritten through the union-find
//! and re-analyzed for simplification opportunities.
//!
//! Reference: CaDiCaL congruence.cpp:4483-4631 (rewrite_and_gate).

use crate::gates::GateType;
use crate::literal::Literal;
use hashbrown::HashMap;
use smallvec::SmallVec;
use std::collections::VecDeque;

use super::super::union_find::{merge_or_contradict, UnionFind};
use super::super::CongruenceStats;
use super::GateSignature;

use super::super::CongruenceClosure;

impl CongruenceClosure {
    /// Rewrite a gate after an equivalence merge (src → dst).
    ///
    /// Replaces all inputs through UF, then performs gate-type-specific analysis:
    /// AND gates check for false inputs, degeneration, complementary pairs.
    /// CaDiCaL congruence.cpp:4483-4631 (rewrite_and_gate) and similar.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::congruence) fn rewrite_gate_after_merge(
        gi: usize,
        gate_types: &mut [GateType],
        gate_inputs: &mut [SmallVec<[usize; 5]>],
        gate_outputs: &mut [usize],
        gate_alive: &mut [bool],
        uf: &mut UnionFind,
        schedule: &mut VecDeque<(usize, usize)>,
        units_to_propagate: &mut VecDeque<usize>,
        unit_vals: &mut [i8],
        discovered_units: &mut Vec<Literal>,
        gate_table: &mut HashMap<GateSignature, usize>,
        occs: &mut [Vec<usize>],
        num_lits: usize,
        stats: &mut CongruenceStats,
        equivalence_edges: &mut Vec<(Literal, Literal)>,
        found_equiv: &mut bool,
    ) -> Result<(), Literal> {
        if !gate_alive[gi] {
            return Ok(());
        }

        Self::remove_gate_signature(gi, gate_types, gate_inputs, gate_table, uf);

        // Rewrite all inputs through UF.
        for inp in &mut gate_inputs[gi] {
            *inp = uf.find(*inp);
        }

        let out = uf.find(gate_outputs[gi]);

        match gate_types[gi] {
            GateType::And => {
                // AND-specific rewriting. CaDiCaL rewrite_and_gate.
                let mut has_false = false;
                let mut has_neg_output = false;
                let mut has_output = false;

                // Remove assigned-true inputs, detect false/degeneration.
                gate_inputs[gi].retain(|inp| {
                    let inp = *inp;
                    let repr = uf.find(inp);
                    let v = if repr < unit_vals.len() {
                        unit_vals[repr]
                    } else {
                        0
                    };
                    if v > 0 {
                        return false; // true: identity
                    }
                    if v < 0 {
                        has_false = true;
                        return false;
                    }
                    if repr == out {
                        has_output = true; // degeneration
                    }
                    if repr == (out ^ 1) {
                        has_neg_output = true;
                    }
                    true
                });

                if has_false || has_neg_output {
                    gate_alive[gi] = false;
                    Self::record_unit(
                        out ^ 1,
                        unit_vals,
                        units_to_propagate,
                        discovered_units,
                        num_lits,
                    )?;
                    return Ok(());
                }

                // Dedup and complementary pair detection.
                gate_inputs[gi].sort_unstable();
                gate_inputs[gi].dedup();
                let has_complement = gate_inputs[gi]
                    .windows(2)
                    .any(|pair| uf.find(pair[0]) == (uf.find(pair[1]) ^ 1));
                if has_complement {
                    gate_alive[gi] = false;
                    Self::record_unit(
                        out ^ 1,
                        unit_vals,
                        units_to_propagate,
                        discovered_units,
                        num_lits,
                    )?;
                    return Ok(());
                }

                match gate_inputs[gi].len() {
                    0 => {
                        gate_alive[gi] = false;
                        Self::record_unit(
                            out,
                            unit_vals,
                            units_to_propagate,
                            discovered_units,
                            num_lits,
                        )?;
                    }
                    1 => {
                        let inp = uf.find(gate_inputs[gi][0]);
                        gate_alive[gi] = false;
                        if inp != out {
                            merge_or_contradict(uf, out, inp, equivalence_edges, stats)?;
                            schedule.push_back((out, inp));
                            *found_equiv = true;
                        }
                    }
                    _ => {
                        if has_output {
                            // Degeneration: output = AND(output, ...) means
                            // output implies all other inputs. Keep for re-hash
                            // but don't produce special units (CaDiCaL tracks
                            // DEGENERATED flag for LRAT; we skip for now).
                        }
                        Self::reinsert_gate(
                            gi,
                            gate_types,
                            gate_inputs,
                            gate_outputs,
                            gate_alive,
                            uf,
                            schedule,
                            gate_table,
                            occs,
                            num_lits,
                            found_equiv,
                        );
                    }
                }
            }
            GateType::Xor => {
                // CaDiCaL-style: inputs positive-normalized, output sign
                // carries XOR/XNOR polarity. parity_flip starts false (#7137).
                // CaDiCaL: negate = 0 (congruence.cpp:4769).
                let mut parity_flip = false;
                gate_inputs[gi].retain(|inp| {
                    let inp = *inp;
                    let repr = uf.find(inp);
                    let v = if repr < unit_vals.len() {
                        unit_vals[repr]
                    } else {
                        0
                    };
                    if v > 0 {
                        parity_flip = !parity_flip;
                        return false;
                    }
                    if v < 0 {
                        return false;
                    }
                    true
                });
                Self::reduce_xor_input_pairs(&mut gate_inputs[gi], uf, &mut parity_flip);

                match gate_inputs[gi].len() {
                    0 => {
                        gate_alive[gi] = false;
                        let unit_lit = if parity_flip { out } else { out ^ 1 };
                        Self::record_unit(
                            unit_lit,
                            unit_vals,
                            units_to_propagate,
                            discovered_units,
                            num_lits,
                        )?;
                    }
                    1 => {
                        let inp = uf.find(gate_inputs[gi][0]);
                        let target = if parity_flip { inp ^ 1 } else { inp };
                        gate_alive[gi] = false;
                        if out != target {
                            merge_or_contradict(uf, out, target, equivalence_edges, stats)?;
                            schedule.push_back((out, target));
                            *found_equiv = true;
                        }
                    }
                    _ => {
                        // Apply accumulated parity to output before reinsertion.
                        // CaDiCaL: lhs sign flip (congruence.cpp:4784). (#7137)
                        if parity_flip {
                            gate_outputs[gi] ^= 1;
                        }
                        Self::reinsert_gate(
                            gi,
                            gate_types,
                            gate_inputs,
                            gate_outputs,
                            gate_alive,
                            uf,
                            schedule,
                            gate_table,
                            occs,
                            num_lits,
                            found_equiv,
                        );
                    }
                }
            }
            GateType::Ite => {
                if gate_inputs[gi].len() == 3 {
                    let cond = uf.find(gate_inputs[gi][0]);
                    let cv = if cond < unit_vals.len() {
                        unit_vals[cond]
                    } else {
                        0
                    };
                    if cv != 0 {
                        let target_idx = if cv > 0 { 1 } else { 2 };
                        let target = uf.find(gate_inputs[gi][target_idx]);
                        gate_alive[gi] = false;
                        if out != target {
                            merge_or_contradict(uf, out, target, equivalence_edges, stats)?;
                            schedule.push_back((out, target));
                            *found_equiv = true;
                        }
                        return Ok(());
                    }
                    // Check if then == else (regardless of condition).
                    let then_repr = uf.find(gate_inputs[gi][1]);
                    let else_repr = uf.find(gate_inputs[gi][2]);
                    if then_repr == else_repr {
                        gate_alive[gi] = false;
                        if out != then_repr {
                            merge_or_contradict(uf, out, then_repr, equivalence_edges, stats)?;
                            schedule.push_back((out, then_repr));
                            *found_equiv = true;
                        }
                        return Ok(());
                    }

                    // Check then/else values for unit/equivalence discovery.
                    // CaDiCaL congruence.cpp:6569-6643 simplify_ite_gate.
                    let v_then = if then_repr < unit_vals.len() {
                        unit_vals[then_repr]
                    } else {
                        0
                    };
                    let v_else = if else_repr < unit_vals.len() {
                        unit_vals[else_repr]
                    } else {
                        0
                    };
                    if v_then != 0 && v_else != 0 {
                        gate_alive[gi] = false;
                        if v_then > 0 && v_else > 0 {
                            // Case A: ITE(c, true, true) = true → unit output
                            Self::record_unit(
                                out,
                                unit_vals,
                                units_to_propagate,
                                discovered_units,
                                num_lits,
                            )?;
                        } else if v_then < 0 && v_else < 0 {
                            // Case B: ITE(c, false, false) = false → unit ¬output
                            Self::record_unit(
                                out ^ 1,
                                unit_vals,
                                units_to_propagate,
                                discovered_units,
                                num_lits,
                            )?;
                        } else if v_then > 0 {
                            // Case C: ITE(c, true, false) = c → output ≡ cond
                            if out != cond {
                                merge_or_contradict(uf, out, cond, equivalence_edges, stats)?;
                                schedule.push_back((out, cond));
                                *found_equiv = true;
                            }
                        } else {
                            // Case D: ITE(c, false, true) = ¬c → output ≡ ¬cond
                            let neg_cond = cond ^ 1;
                            if out != neg_cond {
                                merge_or_contradict(uf, out, neg_cond, equivalence_edges, stats)?;
                                schedule.push_back((out, neg_cond));
                                *found_equiv = true;
                            }
                        }
                        return Ok(());
                    }

                    // ITE→AND/XOR morphing. CaDiCaL rewrite_ite_gate
                    // (congruence.cpp:5656-5960). After morphing, recurse
                    // for full type-specific simplification.
                    //
                    // Guard: only morph when the resulting AND/XOR gate
                    // finds a match in the gate table (enabling a merge).
                    if cond == then_repr {
                        // ITE(c,c,e) = c OR e = NOT(NOT c AND NOT e)
                        let and_inputs = [cond ^ 1, else_repr ^ 1];
                        if Self::morph_would_find_match(&GateType::And, &and_inputs, uf, gate_table)
                        {
                            gate_types[gi] = GateType::And;
                            gate_outputs[gi] = out ^ 1;
                            gate_inputs[gi].clear();
                            gate_inputs[gi].push(and_inputs[0]);
                            gate_inputs[gi].push(and_inputs[1]);
                            stats.ite_to_and += 1;
                            return Self::rewrite_gate_after_merge(
                                gi,
                                gate_types,
                                gate_inputs,
                                gate_outputs,
                                gate_alive,
                                uf,
                                schedule,
                                units_to_propagate,
                                unit_vals,
                                discovered_units,
                                gate_table,
                                occs,
                                num_lits,
                                stats,
                                equivalence_edges,
                                found_equiv,
                            );
                        }
                    }
                    if cond == (then_repr ^ 1) {
                        // ITE(c, NOT c, e) = NOT c AND e
                        let and_inputs = [cond ^ 1, else_repr];
                        if Self::morph_would_find_match(&GateType::And, &and_inputs, uf, gate_table)
                        {
                            gate_types[gi] = GateType::And;
                            gate_inputs[gi].clear();
                            gate_inputs[gi].push(and_inputs[0]);
                            gate_inputs[gi].push(and_inputs[1]);
                            stats.ite_to_and += 1;
                            return Self::rewrite_gate_after_merge(
                                gi,
                                gate_types,
                                gate_inputs,
                                gate_outputs,
                                gate_alive,
                                uf,
                                schedule,
                                units_to_propagate,
                                unit_vals,
                                discovered_units,
                                gate_table,
                                occs,
                                num_lits,
                                stats,
                                equivalence_edges,
                                found_equiv,
                            );
                        }
                    }
                    if cond == else_repr {
                        // ITE(c,t,c) = c AND t
                        let and_inputs = [cond, then_repr];
                        if Self::morph_would_find_match(&GateType::And, &and_inputs, uf, gate_table)
                        {
                            gate_types[gi] = GateType::And;
                            gate_inputs[gi].clear();
                            gate_inputs[gi].push(and_inputs[0]);
                            gate_inputs[gi].push(and_inputs[1]);
                            stats.ite_to_and += 1;
                            return Self::rewrite_gate_after_merge(
                                gi,
                                gate_types,
                                gate_inputs,
                                gate_outputs,
                                gate_alive,
                                uf,
                                schedule,
                                units_to_propagate,
                                unit_vals,
                                discovered_units,
                                gate_table,
                                occs,
                                num_lits,
                                stats,
                                equivalence_edges,
                                found_equiv,
                            );
                        }
                    }
                    if cond == (else_repr ^ 1) {
                        // ITE(c,t,NOT c) = t OR NOT c = NOT(NOT t AND c)
                        let and_inputs = [then_repr ^ 1, cond];
                        if Self::morph_would_find_match(&GateType::And, &and_inputs, uf, gate_table)
                        {
                            gate_types[gi] = GateType::And;
                            gate_outputs[gi] = out ^ 1;
                            gate_inputs[gi].clear();
                            gate_inputs[gi].push(and_inputs[0]);
                            gate_inputs[gi].push(and_inputs[1]);
                            stats.ite_to_and += 1;
                            return Self::rewrite_gate_after_merge(
                                gi,
                                gate_types,
                                gate_inputs,
                                gate_outputs,
                                gate_alive,
                                uf,
                                schedule,
                                units_to_propagate,
                                unit_vals,
                                discovered_units,
                                gate_table,
                                occs,
                                num_lits,
                                stats,
                                equivalence_edges,
                                found_equiv,
                            );
                        }
                    }
                    if then_repr == (else_repr ^ 1) {
                        // ITE(c,t,NOT t) = XOR(c,t) with proper normalization.
                        let mut xor_parity = false;
                        let inp0 = if cond & 1 != 0 {
                            xor_parity = !xor_parity;
                            cond ^ 1
                        } else {
                            cond
                        };
                        let inp1 = if then_repr & 1 != 0 {
                            xor_parity = !xor_parity;
                            then_repr ^ 1
                        } else {
                            then_repr
                        };
                        let xor_inputs = [inp0, inp1];
                        if Self::morph_would_find_match(&GateType::Xor, &xor_inputs, uf, gate_table)
                        {
                            gate_types[gi] = GateType::Xor;
                            gate_outputs[gi] = if xor_parity { out ^ 1 } else { out };
                            gate_inputs[gi].clear();
                            gate_inputs[gi].push(inp0);
                            gate_inputs[gi].push(inp1);
                            stats.ite_to_xor += 1;
                            return Self::rewrite_gate_after_merge(
                                gi,
                                gate_types,
                                gate_inputs,
                                gate_outputs,
                                gate_alive,
                                uf,
                                schedule,
                                units_to_propagate,
                                unit_vals,
                                discovered_units,
                                gate_table,
                                occs,
                                num_lits,
                                stats,
                                equivalence_edges,
                                found_equiv,
                            );
                        }
                    }
                }
                // No morphing applicable: re-hash.
                Self::reinsert_gate(
                    gi,
                    gate_types,
                    gate_inputs,
                    gate_outputs,
                    gate_alive,
                    uf,
                    schedule,
                    gate_table,
                    occs,
                    num_lits,
                    found_equiv,
                );
            }
            GateType::Equiv => {
                // Generic rewrite + re-hash.
                Self::reinsert_gate(
                    gi,
                    gate_types,
                    gate_inputs,
                    gate_outputs,
                    gate_alive,
                    uf,
                    schedule,
                    gate_table,
                    occs,
                    num_lits,
                    found_equiv,
                );
            }
        }
        Ok(())
    }
}
