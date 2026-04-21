// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{EvalRuntimeState, HashMap, OpEvalDeps};
use crate::cache::scope_ids::EvalScopeIds;
use crate::value::{LazyFuncValue, Value};
use crate::var_index::VarRegistry;
use rustc_hash::FxHashSet;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use tla_core::ast::{OperatorDef, Substitution};
use tla_core::name_intern::NameId;

pub(super) static SHARED_CTX_NEXT_ID: AtomicU64 = AtomicU64::new(1);
/// Evaluation environment: variable bindings
pub type Env = HashMap<Arc<str>, Value>;

pub use crate::state_env_ref::{SparseStateEnvRef, StateEnvRef};
pub(crate) use crate::tlc_types::TlcActionContext;
pub use crate::tlc_types::{InstanceInfo, TlcConfig, TlcRuntimeStats};
/// Operator definition storage — canonical definition in `tla_core::OpEnv`.
/// Re-exported here so existing `crate::eval::OpEnv` paths continue to work.
pub use tla_core::OpEnv;

/// Shared immutable context - wrapped in Arc for cheap cloning
/// Contains data that never changes during evaluation (operators, instances, etc.)
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct SharedCtx {
    /// Stable identifier for this shared context (used to scope thread-local caches).
    pub id: u64,
    /// Operator definitions
    pub ops: OpEnv,
    /// Named instances: instance_name -> InstanceInfo
    /// For `InChan == INSTANCE Channel WITH ...`, stores "InChan" -> {module: "Channel", subs: ...}
    pub instances: HashMap<String, InstanceInfo>,
    /// Operators from instanced modules: module_name -> op_name -> OperatorDef
    /// Stores operators from INSTANCE'd modules (not yet substituted)
    pub instance_ops: HashMap<String, OpEnv>,
    /// Variable/constant names that are legal implicit-substitution targets
    /// for each instanced module, in declaration order.
    pub instance_implicit_targets: HashMap<String, Vec<String>>,
    /// Operator replacements: old_name -> new_name (for config `CONSTANT Op <- Replacement`)
    pub op_replacements: HashMap<String, String>,
    /// Variable name registry for O(1) index lookup
    /// Populated once at module load time
    pub var_registry: VarRegistry,
    /// TLC configuration for TLCGet("config")
    pub tlc_config: TlcConfig,
    /// Constants overridden by config file.
    /// When evaluating an identifier, if it's in this set, check env bindings
    /// BEFORE operator definitions. This allows config to override operator
    /// definitions like `Done == CHOOSE v : v \notin Reg` with model values.
    pub config_constants: FxHashSet<String>,
    /// Names of modules imported via EXTENDS (unqualified). Used to scope
    /// builtin overrides: e.g., DyadicRationals.Add should only override
    /// when DyadicRationals is actually extended, not for user-defined Add.
    pub extended_module_names: FxHashSet<String>,
    /// Pre-computed values for zero-arity constant-level operators.
    /// Populated once at setup time (after constants are bound, before BFS).
    /// Enables O(1) lookup in eval_ident, bypassing all cache management,
    /// dep tracking, and context stripping overhead.
    /// Key: NameId (interned operator name) for identity comparison.
    /// Part of #2364 (TLC SpecProcessor.processConstantDefns parity).
    pub precomputed_constants: HashMap<NameId, Value>,
    /// Monotonic version for bytecode/cache invalidation when precomputed
    /// constants are mutated.
    pub precomputed_constants_version: u64,
    /// Union of lowered `[A]_v` / `<<A>>_v` spans from all loaded modules.
    /// Lets property classification preserve TLC's syntactic distinction even
    /// after lowering expands the subscript form to `A \/ UNCHANGED v`.
    pub action_subscript_spans: FxHashSet<tla_core::span::Span>,
    /// Operator names that came from THEOREM/LEMMA declarations.
    /// These are registered as zero-arg operators for reference resolution
    /// (e.g., MCVoting uses `ASSUME QuorumNonEmpty!:`) but must be excluded
    /// from precompute_constant_operators — TLC never evaluates theorem bodies
    /// during model checking (processConstantDefns uses getOpDefs, not
    /// getTheorems). Part of #1105.
    pub theorem_op_names: FxHashSet<String>,
    /// Pre-classified resolution hints for identifiers, indexed by NameId.0.
    ///
    /// Built once at setup time (after precompute_constant_operators and
    /// promote_env_constants_to_precomputed). Each byte classifies what kind
    /// of entity a NameId resolves to, allowing eval_ident to skip the
    /// multi-tier lookup waterfall and jump directly to the correct tier.
    ///
    /// Part of #3961: eliminates 4-7 wasted HashMap/Option checks per
    /// identifier lookup for constants, operators, and builtins.
    pub ident_hints: Vec<IdentHint>,
    /// O(1) NameId-to-VarIndex lookup table, indexed by NameId.0.
    ///
    /// Stores `VarIndex.0` for state variables, or `u16::MAX` for non-state-vars.
    /// Replaces the linear scan in `VarRegistry::get_by_name_id()` on the eval_ident
    /// hot path. Built alongside `ident_hints` in `build_ident_hints`.
    ///
    /// Part of #3961: state variable lookup is the hottest path in BFS evaluation.
    /// Each call to `get_by_name_id()` linearly scans `name_id_indices` (typically
    /// <20 entries but called millions of times). This table converts the linear
    /// scan to a single array index.
    pub var_idx_by_name_id: Vec<u16>,
    /// O(1) NameId-to-OperatorDef lookup table, indexed by NameId.0.
    ///
    /// Stores `Some(Arc<OperatorDef>)` for names that resolve to shared operators,
    /// `None` for non-operators. Replaces string-hashed `ops.get(name)` lookups
    /// in eval_ident's SharedZeroArgOp hint path and waterfall fallback.
    ///
    /// Part of #3961: string-hashed HashMap lookups (SipHash + bucket probe) are
    /// the remaining bottleneck after hint classification. This table converts
    /// them to a bounds check + array index. Built alongside `ident_hints`.
    pub ops_by_name_id: Vec<Option<Arc<OperatorDef>>>,
}

/// Resolution hint for an identifier, classifying what kind of entity it resolves to.
///
/// Used by eval_ident to skip the multi-tier lookup waterfall. After BindingChain
/// lookup (which handles quantifier vars and LET bindings), the hint tells eval_ident
/// which tier to check directly instead of cascading through op_replacements,
/// let_def_overlay, local_ops, precomputed_constants, env, shared.ops, and builtins.
///
/// Part of #3961.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum IdentHint {
    /// Unknown resolution — use the full waterfall (default for unclassified names).
    Unknown = 0,
    /// Resolves to a precomputed constant (SharedCtx.precomputed_constants).
    PrecomputedConstant = 1,
    /// Resolves to a zero-arg shared operator (SharedCtx.ops, zero params).
    SharedZeroArgOp = 2,
    /// Resolves to a shared operator with parameters (SharedCtx.ops, non-zero params).
    /// Not directly evaluable by eval_ident — will be handled by Apply.
    SharedParamOp = 3,
    /// Resolves to a builtin (Nat, Int, BOOLEAN, etc.).
    Builtin = 4,
    /// Has an operator replacement configured (op_replacements).
    /// Must go through slow path to resolve the replacement chain.
    OpReplacement = 5,
    /// Resolves to a state variable (should normally be Expr::StateVar, not Expr::Ident).
    StateVar = 6,
}

impl SharedCtx {
    /// Create a new shared context
    pub fn new() -> Self {
        SharedCtx {
            id: SHARED_CTX_NEXT_ID.fetch_add(1, Ordering::Relaxed),
            ops: HashMap::new(),
            instances: HashMap::new(),
            instance_ops: HashMap::new(),
            instance_implicit_targets: HashMap::new(),
            op_replacements: HashMap::new(),
            var_registry: VarRegistry::new(),
            tlc_config: TlcConfig::default(),
            config_constants: FxHashSet::default(),
            extended_module_names: FxHashSet::default(),
            precomputed_constants: HashMap::new(),
            precomputed_constants_version: 0,
            action_subscript_spans: FxHashSet::default(),
            theorem_op_names: FxHashSet::default(),
            ident_hints: Vec::new(),
            var_idx_by_name_id: Vec::new(),
            ops_by_name_id: Vec::new(),
        }
    }

    // SharedCtx field accessor methods extracted to eval_ctx_ops.rs (Part of #2764)

    /// Create a shared context with a pre-populated variable registry
    pub fn with_var_registry(var_registry: VarRegistry) -> Self {
        SharedCtx {
            id: SHARED_CTX_NEXT_ID.fetch_add(1, Ordering::Relaxed),
            ops: HashMap::new(),
            instances: HashMap::new(),
            instance_ops: HashMap::new(),
            instance_implicit_targets: HashMap::new(),
            op_replacements: HashMap::new(),
            var_registry,
            tlc_config: TlcConfig::default(),
            config_constants: FxHashSet::default(),
            extended_module_names: FxHashSet::default(),
            precomputed_constants: HashMap::new(),
            precomputed_constants_version: 0,
            action_subscript_spans: FxHashSet::default(),
            theorem_op_names: FxHashSet::default(),
            ident_hints: Vec::new(),
            var_idx_by_name_id: Vec::new(),
            ops_by_name_id: Vec::new(),
        }
    }
}

impl Default for SharedCtx {
    fn default() -> Self {
        Self::new()
    }
}

/// Evaluation context
///
/// The context is split into two parts for efficient cloning:
/// - `shared`: Arc-wrapped immutable data (operators, instances) - O(1) clone
/// - `env`, `next_state`, `local_ops`: Per-evaluation mutable data
///
/// For performance during state enumeration, temporary bindings can be pushed
/// to `local_stack` using `push_binding()` and restored using `pop_to_mark()`.
/// This avoids HashMap allocation overhead for millions of state transitions.
/// Maximum recursion depth for function evaluation.
/// This prevents stack overflow when evaluating deeply recursive TLA+ functions
/// like `f[i \in 0..N] == ... f[i-1] ...`. TLC default is 100.
/// Part of #1275: Lowered from 500 to 100 to match TLC and prevent stack overflow
/// in debug builds where large eval frames can exhaust the stack before stacker
/// can grow it (stacker check only runs every 256 evals).
pub const MAX_RECURSION_DEPTH: u32 = 100;

/// Cold fields that change at module/operator/state boundaries, NOT per binding.
///
/// Part of #2955: Wrapped in `Rc` for O(1) clone during RECURSIVE evaluation.
/// Instead of copying 16 fields per recursion level, a single Rc refcount bump
/// shares the entire stable context. This follows the hot/cold split design:
/// `designs/2026-03-03-evalctx-cold-hot-split-for-recursive.md`.
#[derive(Clone)]
pub struct EvalCtxStable {
    /// Shared immutable context (Arc-wrapped for cheap cloning)
    pub(crate) shared: Arc<SharedCtx>,
    /// Mutable per-evaluation runtime state shared across cloned contexts.
    pub(crate) runtime_state: Rc<EvalRuntimeState>,
    /// Variable environment (base bindings)
    /// Arc-wrapped for O(1) clone during ctx.clone() on BFS hot path (Part of #1383).
    /// Mutations use Arc::make_mut for copy-on-write (no-op when refcount == 1).
    pub(crate) env: Arc<Env>,
    /// Next-state values for resolving primed variables (x' -> value)
    /// Arc-wrapped for cheap cloning during bind()
    pub(crate) next_state: Option<Arc<Env>>,
    /// Local operator definitions (from LET expressions)
    /// These shadow the shared ops
    /// Arc-wrapped for cheap cloning during bind()
    pub(crate) local_ops: Option<Arc<OpEnv>>,
    /// Array-based state variable storage for O(1) access.
    ///
    /// This points at the current state's `[Value]` array (usually from `ArrayState`)
    /// and is only valid while the caller keeps that array alive. This avoids
    /// per-state cloning/allocation in the BFS hot path.
    pub(crate) state_env: Option<StateEnvRef>,
    /// Array-based next-state variable storage for O(1) primed variable access.
    ///
    /// Similar to `state_env`, but for next-state values (primed variables like x').
    /// Used by `prime_guards_hold_in_next_array` to avoid HashMap construction overhead.
    pub(crate) next_state_env: Option<StateEnvRef>,
    /// Active INSTANCE substitutions for the current evaluation scope.
    ///
    /// When evaluating an operator from an instanced module (e.g., `C!Spec`), we store the
    /// substitutions applied to that instance so nested instances inside that module can
    /// inherit them (TLC composes substitutions through nested INSTANCE declarations).
    pub(crate) instance_substitutions: Option<Arc<Vec<Substitution>>>,
    /// Part of #2980: Content hash of parametrized INSTANCE argument values.
    ///
    /// When `P(Succ) == INSTANCE M` is evaluated as `P(f)!Op`, the evaluated
    /// argument values are hashed and stored here. The EAGER_BINDINGS_CACHE key
    /// includes this hash to disambiguate cache entries by argument values,
    /// preventing stale cache hits when the same callsite is invoked with
    /// different argument values (e.g., `\A Succ \in SuccSet : P(Succ)!Op`).
    ///
    /// Zero when no parametrized INSTANCE is active (non-parametrized callers).
    pub(crate) param_args_hash: u64,
    // call_by_name_subs: moved to hot EvalCtx struct (Part of #2956).
    // Setting/clearing this field previously triggered Rc::make_mut on every
    // without_call_by_name_subs() call (~16 Arc bumps per parameter reference).
    // Now it's a direct field set on the hot struct with zero Rc overhead.
    /// Part of #203: Skip prime validation for the current operator subtree.
    pub(crate) skip_prime_validation: bool,
    /// Current BFS exploration level for TLCGet("level").
    ///
    /// Part of #254: Animation specs like EWD840_anim use TLCGet("level") to
    /// display the current exploration depth in SVG output. Set this before
    /// evaluating actions/invariants at each BFS depth.
    pub(crate) tlc_level: u32,
    /// Pre-built TLCExt!Trace value for the current behavior prefix.
    ///
    /// Part of #1117: Animation/debugging specs use TLCExt!Trace to access the
    /// current trace (sequence of states from Init to current). This is set by
    /// the model checker before evaluating invariants/actions when Trace is used.
    /// Format: Tuple([Record(var->val), ...]) where each record is a state.
    pub(crate) tlc_trace_value: Option<Arc<Value>>,
    /// Part of #2330: When true, substitution RHS evaluation preserves local_ops
    /// and sibling substitutions instead of clearing to global context.
    ///
    /// Set by `eval_chained_module_ref` when evaluating a multi-level chain like
    /// `A!B!C!D`. Composed substitutions in chained refs mix entries from different
    /// scope levels, so the RHS of a substitution may reference operators from
    /// intermediate modules (via local_ops) or variables from other substitution
    /// levels. Without this flag, `with_outer_resolution_scope()` clears
    /// everything, causing "Undefined variable" errors for intermediate names.
    pub(crate) chained_ref_eval: bool,
    /// Fix #2364: Pre-evaluated INSTANCE substitution bindings for O(1) bypass.
    ///
    /// Built at INSTANCE scope entry (eval_module_ref / eval_chained_module_ref) by
    /// eagerly evaluating each substitution RHS to a (NameId, Value, OpEvalDeps) triple.
    /// eval_ident and eval_state_var use this to bypass SUBST_CACHE entirely: if the name
    /// matches a binding, return the pre-computed value directly (propagating deps for
    /// cache correctness). If the name is NOT in the set, skip SUBST_CACHE entirely
    /// (the name can't be a substitution target). This eliminates SUBST_CACHE overhead
    /// for ALL identifiers in INSTANCE scope — critical for specs with deep INSTANCE
    /// chains like EWD998ChanID.
    pub(crate) eager_subst_bindings: Option<Arc<Vec<(NameId, Value, OpEvalDeps)>>>,
    /// Part of #2991: Pre-module-scope binding chain snapshot.
    ///
    /// Saved by `with_module_scope_shared`/`with_module_scope_arced_subs` before
    /// pushing module-scope operator param bindings. Used by `build_eager_subst_bindings`
    /// to evaluate substitution RHS in the outer-module context while preserving
    /// parametrized INSTANCE param bindings (e.g., `Succ` in `P(Succ) == INSTANCE M`).
    ///
    /// Without this, `with_outer_resolution_scope()` clears the chain entirely,
    /// losing param bindings that were previously stored in env (which wasn't cleared).
    pub(crate) pre_scope_bindings: Option<crate::binding_chain::BindingChain>,
    /// Part of #3056 Phase B: Pre-module-scope local_ops snapshot.
    ///
    /// Saved by `with_module_scope_shared`/`with_module_scope_arced_subs` before
    /// merging the inner module's operators. Used by `force_lazy_binding` to
    /// evaluate substitution RHS in the correct operator scope: the enclosing
    /// module's operators (pre-merge), not the merged operators (which would let
    /// inner module operators shadow the substitution target).
    ///
    /// Matches TLC: evalImplSubstInKind evaluates sub RHS with `c` (the context
    /// at SubstIn entry), before the inner module's context is pushed.
    pub(crate) pre_scope_local_ops: Option<Arc<OpEnv>>,
    /// Part of #3099: Stable scope identity for cache keys.
    ///
    /// Content-based u64 fingerprints for `local_ops` and `instance_substitutions`.
    /// Computed once at scope construction time. Cache key builders read these ids
    /// instead of deriving scope identity from `Arc::as_ptr()`, enabling cache hits
    /// across reconstructed but logically identical scopes.
    pub(crate) scope_ids: EvalScopeIds,
}

/// Implements `Deref` so that cold field reads (`ctx.env`, `ctx.shared`, etc.)
/// auto-resolve through the Rc without any code changes at ~400+ read sites.
/// Write access requires explicit `ctx.stable_mut().field = value`.
impl std::ops::Deref for EvalCtx {
    type Target = EvalCtxStable;

    #[inline(always)]
    fn deref(&self) -> &EvalCtxStable {
        &self.stable
    }
}

#[non_exhaustive]
pub struct EvalCtx {
    /// Cold fields: Rc-clone = 1 refcount bump (Part of #2955).
    /// Contains fields that change at module/state boundaries but NOT per binding.
    pub(crate) stable: Rc<EvalCtxStable>,
    /// Hot: Logical depth of local bindings for mark/pop restoration.
    ///
    /// Part of #2955: Replaces `local_stack.len()` as the scope position tracker.
    /// BindingChain is now the sole source of truth for local binding data;
    /// this counter provides the depth index for StackMark save/restore and
    /// record_local_read's outer-scope vs inner-variable classification.
    pub(crate) binding_depth: usize,
    /// Hot: Part of #188, #2956: Call-by-name parameter substitutions for operators
    /// with primed parameters.
    ///
    /// Moved from EvalCtxStable to EvalCtx (Part of #2956) because
    /// `without_call_by_name_subs()` is called on EVERY parameter reference in
    /// call-by-name operators. When in the Rc-shared stable struct, each call
    /// triggered `Rc::make_mut` (~16 Arc bumps + EvalCtxStable clone when shared).
    /// Now it's a direct field set with zero Rc overhead.
    pub(crate) call_by_name_subs: Option<Arc<Vec<Substitution>>>,
    /// Current TLC action metadata for `TLCGet("action")`.
    ///
    /// Kept on the hot context because it changes at operator-entry boundaries,
    /// not at module/state boundaries.
    pub(crate) tlc_action_context: Option<Arc<TlcActionContext>>,
    /// Hot: Current recursion depth for lazy function evaluation.
    ///
    /// Part of #3395: Self-recursive LazyFunc calls update this field on every
    /// level. Keeping it on `EvalCtx` avoids `Rc::make_mut` + `EvalCtxStable`
    /// clone in the fast path.
    pub(crate) recursion_depth: u32,
    /// Hot: Exact lazy function instance currently being evaluated, if any.
    ///
    /// Part of #3395: The self-recursive LazyFunc fast path is only sound when
    /// the caller is already evaluating the same `LazyFuncValue` instance.
    /// Keeping this on `EvalCtx` avoids cloning `EvalCtxStable` just to swap the
    /// active function marker at recursive call boundaries.
    pub(crate) active_lazy_func: Option<Arc<LazyFuncValue>>,
    /// Hot: Part of #2364: Unified binding chain — TLC `Context` parity.
    ///
    /// Single immutable persistent linked list containing ALL local bindings
    /// (quantifier variables, LET definitions, operator parameters). Lookup walks
    /// the chain using NameId integer equality. "Cloning" is Rc::clone of the head.
    ///
    /// Part of #2955: Now the SOLE source of truth for local bindings, replacing
    /// the previous triple-write to local_stack + BindingChain + env.
    pub(super) bindings: crate::binding_chain::BindingChain,
    /// Hot: Part of #1093: Lightweight overlay chain for zero-arg LET operator defs.
    ///
    /// Checked by `get_op()` before `local_ops`. Avoids cloning the entire
    /// `OpEnv` HashMap for LETs that only contain zero-arg defs (scalar,
    /// recursive FuncDef, InstanceExpr). Matches TLC's `Context.cons(...)`
    /// for cheap zero-arg LET context extension.
    ///
    /// On `EvalCtx` (hot) not `EvalCtxStable` (cold): pushing to the overlay is
    /// a direct field set, no `Rc::make_mut` needed.
    pub(super) let_def_overlay: crate::let_def_chain::LetDefOverlay,
    /// Hot: Part of #3365: Borrowed sparse next-state overlay from ENABLED
    /// WitnessState. When set, primed reads consult this before HashMap fallback.
    /// `None` slots = unbound (fall through to current state).
    /// On `EvalCtx` (hot) not `EvalCtxStable` (cold) so binding it is a direct
    /// field write, no `Rc::make_mut` needed.
    pub sparse_next_state_env: Option<SparseStateEnvRef>,
    // chain_snapshots removed — Part of #2955 Step 3: mark_stack() now returns
    // a StackMark that captures the chain head directly. O(1) save + O(1) restore,
    // eliminating per-push snapshot overhead and Vec allocation from EvalCtx::clone().
    // fast_locals removed — Part of #2895 Step 4: Merged into BindingChain.
    // The compiled path now uses push_binding_preinterned / mark_stack / pop_to_mark
    // (same as AST path), eliminating the dual lookup tier and Vec clone from
    // EvalCtx::clone(). get_local_by_depth delegates directly to the chain.
}

// RAII guards (NextStateEnvGuard, StateEnvGuard, SkipPrimeValidationGuard, ScopeGuard)
// extracted to eval_ctx_guards.rs (Part of #2764)

impl EvalCtx {
    /// Create a new evaluation context
    pub fn new() -> Self {
        EvalCtx {
            stable: Rc::new(EvalCtxStable {
                shared: Arc::new(SharedCtx::new()),
                runtime_state: Rc::new(EvalRuntimeState::new()),
                env: Arc::new(HashMap::new()),
                next_state: None,
                local_ops: None,
                state_env: None,
                next_state_env: None,
                instance_substitutions: None,
                param_args_hash: 0,
                skip_prime_validation: false,
                tlc_level: 0,
                tlc_trace_value: None,
                chained_ref_eval: false,
                eager_subst_bindings: None,
                pre_scope_bindings: None,
                pre_scope_local_ops: None,
                scope_ids: EvalScopeIds::default(),
            }),
            binding_depth: 0,
            call_by_name_subs: None,
            tlc_action_context: None,
            recursion_depth: 0,
            active_lazy_func: None,
            bindings: crate::binding_chain::BindingChain::empty(),
            let_def_overlay: crate::let_def_chain::LetDefOverlay::empty(),
            sparse_next_state_env: None,
        }
    }

    /// Create context with variable bindings
    pub fn with_env(env: Env) -> Self {
        EvalCtx {
            stable: Rc::new(EvalCtxStable {
                shared: Arc::new(SharedCtx::new()),
                runtime_state: Rc::new(EvalRuntimeState::new()),
                env: Arc::new(env),
                next_state: None,
                local_ops: None,
                state_env: None,
                next_state_env: None,
                instance_substitutions: None,
                param_args_hash: 0,
                skip_prime_validation: false,
                tlc_level: 0,
                tlc_trace_value: None,
                chained_ref_eval: false,
                eager_subst_bindings: None,
                pre_scope_bindings: None,
                pre_scope_local_ops: None,
                scope_ids: EvalScopeIds::default(),
            }),
            binding_depth: 0,
            call_by_name_subs: None,
            tlc_action_context: None,
            recursion_depth: 0,
            active_lazy_func: None,
            bindings: crate::binding_chain::BindingChain::empty(),
            let_def_overlay: crate::let_def_chain::LetDefOverlay::empty(),
            sparse_next_state_env: None,
        }
    }

    /// Get mutable access to the stable (cold) fields via copy-on-write.
    ///
    /// Part of #2955: Rc::make_mut clones EvalCtxStable only when the Rc
    /// refcount > 1 (i.e., shared with parent). When refcount == 1 (unique
    /// owner), returns a direct &mut reference with no allocation.
    #[inline(always)]
    pub(crate) fn stable_mut(&mut self) -> &mut EvalCtxStable {
        Rc::make_mut(&mut self.stable)
    }

    // Context clone-and-modify methods (with_next_state, with_state_envs)
    // extracted to eval_ctx_ops.rs (Part of #2764)

    // Binding methods (bind, bind2, bind3, bind_many, bind_local, bind_all,
    // into_bind*, bind_shadow_aware) and scope management methods (with_local_ops,
    // with_instance_substitutions, with_call_by_name_subs, without_*, with_module_scope,
    // with_instance_scope) extracted to eval_ctx_bind.rs

    // Mutation methods, field accessors, lookup, operator methods, and scope guards
    // extracted to eval_ctx_ops.rs (Part of #2764)

    /// Part of #3063: Shared stacker throttle for both eval_dispatch and compiled guard
    /// hot paths. Increments the counter and returns whether the caller should check
    /// stack depth (every 64th call in release, every call in debug).
    #[inline(always)]
    pub fn should_check_stack(&self) -> bool {
        let count = self
            .stable
            .runtime_state
            .stacker_counter
            .get()
            .wrapping_add(1);
        self.stable.runtime_state.stacker_counter.set(count);
        #[cfg(debug_assertions)]
        {
            true
        }
        #[cfg(not(debug_assertions))]
        {
            (count & 0x3f) == 0
        }
    }
}

impl Default for EvalCtx {
    fn default() -> Self {
        Self::new()
    }
}

// Cache lifecycle (stack_safe, eval_entry, force_lazy_thunk_if_needed) extracted
// to eval_cache_lifecycle.rs
// Eval dispatch (eval, eval_inner, eval_expr) extracted to eval_dispatch.rs

impl Clone for EvalCtx {
    fn clone(&self) -> Self {
        // Part of #2955, #2895: Thin-context clone — 1 Rc bump + 1 usize copy + 1 Arc clone.
        // BindingChain (Arc cons-list) is the sole source of local binding data.
        // fast_locals Vec eliminated (Part of #2895 Step 4): no Vec clone needed.
        EvalCtx {
            stable: Rc::clone(&self.stable),
            binding_depth: self.binding_depth,
            call_by_name_subs: self.call_by_name_subs.clone(),
            tlc_action_context: self.tlc_action_context.clone(),
            recursion_depth: self.recursion_depth,
            active_lazy_func: self.active_lazy_func.clone(),
            bindings: self.bindings.clone(),
            let_def_overlay: self.let_def_overlay.clone(),
            sparse_next_state_env: self.sparse_next_state_env,
        }
    }
}
