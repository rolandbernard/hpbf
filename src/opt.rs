//! Optimizer for the internal IR. Performs mostly constant propagation,
//! loop analysis, and dead code elimination.

use std::mem;

use crate::{
    hasher::{HashMap, HashSet},
    ir::{Block, Expr, Instr, Program},
    smallvec::SmallVec,
    CellType,
};

/// A write can either be known, unknown. A write that is not guaranteed to happen
/// is encoded with [`OptWrite::Maybe`], while a write that is guaranteed to happen,
/// but for which we don't know the value is encoded with [`OptWrite::Unknown`].
enum OptWrite<C: CellType> {
    Known(Expr<C>),
    Unknown,
    Maybe,
}

/// Fallback for comparison and constant lookup.
enum OptParent<'a, C: CellType> {
    Zero,
    Unknown,
    Parent(&'a OptRebuild<'a, C>),
}

/// State for rebuilding a single block. Includes both the already emitted instructions,
/// their effect, and all the pending operations.
struct OptRebuild<'a, C: CellType> {
    parent: OptParent<'a, C>,
    anal: Option<OptAnalysis<C>>,
    shift: isize,
    cond: Option<isize>,
    sub_shift: bool,
    no_return: bool,
    reads: HashSet<isize>,
    written: HashMap<isize, OptWrite<C>>,
    pending: HashMap<isize, Expr<C>>,
    reverse: HashMap<isize, HashSet<isize>>,
    insts: Vec<Instr<C>>,
    sub_anal: Vec<OptAnalysis<C>>,
}

/// Type representing the number of times a loop will be executed. This value
/// is conservatively computed as part of the optimizer analysis.
struct OptLoop<C: CellType> {
    never: bool,
    finite: bool,
    no_effect: bool,
    no_continue: bool,
    at_least_once: bool,
    at_most_once: bool,
    expr: Option<Expr<C>>,
}

/// This is the information that we transfer from one rebuild iteration to the next.
struct OptAnalysis<C: CellType> {
    loop_anal: OptLoop<C>,
    has_shift: bool,
    reads: HashSet<isize>,
    clobbered: HashSet<isize>,
    sub_blocks: Vec<OptAnalysis<C>>,
}

/// Type for holding the state during dead store elimination.
struct OptDseState<'a, C: CellType> {
    parent: Option<&'a OptDseState<'a, C>>,
    shift: isize,
    had_shift: bool,
    anal: &'a OptAnalysis<C>,
    reads: HashSet<isize>,
    written: HashSet<isize>,
}

impl<'a, C: CellType> OptLoop<C> {
    /// Runs exactly as often as indicated by `expr` evaluated before the loop.
    fn expr(expr: Expr<C>) -> Self {
        let constant = expr.constant();
        OptLoop {
            never: constant == Some(C::ZERO),
            finite: true,
            no_continue: false,
            no_effect: constant == Some(C::ZERO),
            at_least_once: matches!(constant, Some(c) if c != C::ZERO),
            at_most_once: matches!(constant, Some(c) if c == C::ZERO || c == C::ONE),
            expr: Some(expr),
        }
    }

    /// The loop will never complete a single iteration.
    fn no_return(at_least_once: bool) -> Self {
        OptLoop {
            never: false,
            finite: true,
            no_effect: true,
            no_continue: at_least_once,
            at_least_once,
            at_most_once: true,
            expr: if at_least_once {
                Some(Expr::val(C::ONE))
            } else {
                None
            },
        }
    }

    /// The loop will repeat infinitely if it runs at least once.
    fn infinite(at_least_once: bool) -> Self {
        OptLoop {
            never: false,
            finite: false,
            no_effect: true,
            no_continue: at_least_once,
            at_least_once,
            at_most_once: false,
            expr: None,
        }
    }

    /// The loop runs at most once, put possibly never.
    fn at_most_once(at_least_once: bool) -> Self {
        if at_least_once {
            Self::expr(Expr::val(C::ONE))
        } else {
            OptLoop {
                never: false,
                finite: true,
                no_effect: false,
                no_continue: false,
                at_least_once: false,
                at_most_once: true,
                expr: None,
            }
        }
    }

    /// We are unable to analyze the loop. This is the most conservative estimate
    /// that must always be sound to use, regardless of the loop.
    fn unknown(at_least_once: bool) -> Self {
        OptLoop {
            never: false,
            finite: false,
            no_effect: false,
            no_continue: false,
            at_least_once,
            at_most_once: false,
            expr: None,
        }
    }

    /// Convert this loop analysis to an at least once type. Used when wrapping
    /// the loop in an if.
    fn to_at_least_once(&self) -> Self {
        OptLoop {
            never: self.never,
            finite: self.finite,
            no_effect: self.no_effect,
            no_continue: self.no_continue,
            at_least_once: true,
            at_most_once: self.at_most_once,
            expr: self.expr.clone(),
        }
    }

    /// Convert this loop analysis to an at most once type. Used for the wrapping
    /// if during rebuilding.
    fn to_at_most_once(&self) -> Self {
        OptLoop {
            never: self.never,
            finite: true,
            no_effect: self.no_effect,
            no_continue: self.no_continue,
            at_least_once: self.at_least_once,
            at_most_once: true,
            expr: None,
        }
    }
}

impl<'a, C: CellType> OptRebuild<'a, C> {
    /// Remove the pending operation for the variable `var`. Return the operation
    /// that was pending, if there was any.
    fn remove_pending(&mut self, var: isize) -> Option<Expr<C>> {
        if let Some(expr) = self.pending.remove(&var) {
            for v in expr.variables() {
                if let Some(users) = self.reverse.get_mut(&v) {
                    users.remove(&var);
                    if users.is_empty() {
                        self.reverse.remove(&v);
                    }
                }
            }
            Some(expr)
        } else {
            None
        }
    }

    /// Insert a new pending operation for `var` to perform `expr`.
    fn insert_pending(&mut self, var: isize, expr: Expr<C>) {
        self.remove_pending(var);
        if !self.compare_written_no_parent(Expr::var(var), &expr) {
            let expr = expr.normalize();
            for v in expr.variables().filter(|&x| x != var) {
                let users = self.reverse.entry(v).or_insert(HashSet::new());
                users.insert(var);
            }
            self.pending.insert(var, expr);
        }
    }

    /// Insert a new known cell operation.
    fn insert_written(&mut self, var: isize, val: OptWrite<C>) {
        if let OptWrite::Known(expr) = val {
            self.written.insert(var, OptWrite::Known(expr.normalize()));
        } else {
            self.written.insert(var, val);
        }
    }

    /// Get the current operation that has been performed to the variable `var`
    /// relative to the start of the block. If the result would depend on a
    /// clobbered value, return [`None`].
    fn get_written(&self, var: isize) -> Option<Expr<C>> {
        if let Some(write) = self.written.get(&var) {
            if let OptWrite::Known(expr) = write {
                Some(expr.clone())
            } else {
                None
            }
        } else if let Some(val) = self.get_parent_constant(var) {
            Some(Expr::val(val))
        } else {
            Some(Expr::var(var))
        }
    }

    /// Get the pending operation for the given variable. If there is no operation
    /// pending for var, return the identity expression.
    fn get_pending(&self, var: isize) -> Expr<C> {
        if let Some(expr) = self.pending.get(&var) {
            expr.clone()
        } else if let Some(val) = self.get_written_constant(var) {
            Expr::val(val)
        } else {
            Expr::var(var)
        }
    }

    /// If the value to be output has already been written into a different cell,
    /// return that cell. Otherwise return [`None`].
    fn retarget_output(&self, var: isize) -> Option<isize> {
        if let Some(expr) = self.pending.get(&var) {
            if let Some(var) = expr.identity() {
                Some(var)
            } else {
                None
            }
        } else {
            Some(var)
        }
    }

    /// Get the combination of pending and written operations performed for the
    /// given variable since the start of the block, or [`None`] if unknown.
    fn get(&self, var: isize) -> Option<Expr<C>> {
        if let Some(expr) = self.pending.get(&var) {
            self.eval_written(expr)
        } else {
            self.get_written(var)
        }
    }

    /// Return true whether the parent context may be consulted for comparing or
    /// evaluating the given variable `var`.
    fn can_ask_parent_for(&self, var: isize) -> bool {
        !self.sub_shift
            && matches!(&self.anal, Some(anal)
            if anal.loop_anal.at_most_once
                || (!anal.clobbered.contains(&(var - self.shift)) && !anal.has_shift))
    }

    /// Get the constant value from the parent context, if there is one.
    fn get_parent_constant(&self, var: isize) -> Option<C> {
        if self.can_ask_parent_for(var) {
            if let OptParent::Zero = self.parent {
                Some(C::ZERO)
            } else if let OptParent::Parent(parent) = self.parent {
                parent.get_constant(var)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// If the variable `var` is known to have a constant value already written
    /// to it, return that value, otherwise return [`None`].
    fn get_written_constant(&self, var: isize) -> Option<C> {
        if let Some(write) = self.written.get(&var) {
            if let OptWrite::Known(expr) = write {
                expr.constant()
            } else {
                None
            }
        } else {
            self.get_parent_constant(var)
        }
    }

    /// If the variable `var` is known to have a constant value pending or
    /// written to it, return that value, otherwise return [`None`].
    fn get_constant(&self, var: isize) -> Option<C> {
        if let Some(expr) = self.pending.get(&var) {
            expr.constant()
        } else {
            self.get_written_constant(var)
        }
    }

    /// Returns true if the value of `var` is known to be non-zero.
    fn is_non_zero(&self, var: isize) -> bool {
        if let Some(expr) = self.pending.get(&var) {
            expr.constant().is_some_and(|c| c != C::ZERO)
        } else if let Some(write) = self.written.get(&var) {
            matches!(write, OptWrite::Known(expr) if expr.constant().is_some_and(|c| c != C::ZERO))
        } else if !self.sub_shift && self.cond == Some(var) {
            true
        } else if self.can_ask_parent_for(var) {
            if let OptParent::Parent(parent) = self.parent {
                parent.is_non_zero(var)
            } else {
                false
            }
        } else {
            false
        }
    }

    /// Perform the calculations `calcs`, offset by `shift`, at the same time on
    /// the current state. This will not emit any instructions, but only add
    /// the necessary pending operations.
    fn perform_all(&mut self, shift: isize, calcs: &[(isize, Expr<C>)]) {
        let mut exprs = SmallVec::<_, 1>::with_capacity(calcs.len());
        for (var, expr) in calcs {
            // Special check to avoid the worst type of exponential explosion.
            for vars in expr.grouped_vars() {
                if vars.len() >= 2 {
                    let mut last = isize::MIN;
                    for &var in vars {
                        if let Some(expr) = self.pending.get(&var) {
                            if expr.add_count() > 1 || (last == var && expr.op_count() > 1) {
                                self.emit(var);
                            }
                        }
                        last = var;
                    }
                }
            }
            let pending = self.eval_pending(shift, expr);
            exprs.push((shift + *var, pending));
        }
        for (var, expr) in exprs {
            self.insert_pending(var, expr);
        }
    }

    /// DFS over the dependency graph to construct topologically sorted list of
    /// strongly connected components.
    fn gather_to_emit_dfs(
        &mut self,
        var: isize,
        index: &mut usize,
        visited: &mut HashMap<isize, usize>,
        stack: &mut Vec<(isize, Option<Expr<C>>)>,
        comps: &mut Vec<SmallVec<(isize, Expr<C>), 1>>,
    ) -> usize {
        let cur_index = *index;
        *index += 1;
        visited.insert(var, cur_index);
        let stack_len = stack.len();
        let mut low = cur_index;
        if let Some(next) = self.reverse.get(&var) {
            for n in next.iter().copied().collect::<Vec<_>>() {
                if let Some(v) = visited.get(&n) {
                    low = low.min(*v);
                } else {
                    let reached = self.gather_to_emit_dfs(n, index, visited, stack, comps);
                    low = low.min(reached);
                }
            }
        }
        stack.push((var, self.remove_pending(var)));
        if low == cur_index {
            let mut new_comp = SmallVec::with_capacity(stack.len() - stack_len);
            while stack.len() != stack_len {
                let elem = stack.pop().unwrap();
                visited.insert(elem.0, usize::MAX);
                if let Some(expr) = elem.1 {
                    new_comp.push((elem.0, expr));
                }
            }
            if !new_comp.is_empty() {
                comps.push(new_comp);
            }
        }
        return low;
    }

    /// Emitting a pending operation might necessitate either emitting or adjusting
    /// other pending operations. This function performs the necessary steps and
    /// returns the operations that must be performed grouped by, and in the order
    /// in which they must be emitted.
    fn gather_for_emit(&mut self, emit: &[isize]) -> Vec<SmallVec<(isize, Expr<C>), 1>> {
        let mut comps = Vec::new();
        if emit.iter().all(|var| !self.reverse.contains_key(var)) {
            // Optimize the common case where no one depends on anyone else.
            for &var in emit {
                if let Some(pending) = self.remove_pending(var) {
                    comps.push(SmallVec::with((var, pending)));
                }
            }
        } else {
            let mut visited = HashMap::with_capacity(2 * emit.len());
            let mut stack = Vec::with_capacity(4);
            for &var in emit {
                if !visited.contains_key(&var) {
                    self.gather_to_emit_dfs(var, &mut 0, &mut visited, &mut stack, &mut comps);
                }
            }
        }
        return comps;
    }

    /// Record the execution of the given operations.
    fn written_calcs(
        &mut self,
        calcs: impl Iterator<Item = (isize, impl Into<Expr<C>> + AsRef<Expr<C>>)>,
    ) {
        let mut knowns = SmallVec::<_, 1>::with_capacity(calcs.size_hint().0);
        for (var, calc) in calcs {
            // Special check to avoid overly large expressions.
            if calc.as_ref().op_count() < 32 {
                if let Some(calc) = self.eval_written(calc) {
                    knowns.push((var, OptWrite::Known(calc)));
                } else {
                    knowns.push((var, OptWrite::Unknown));
                }
            } else {
                knowns.push((var, OptWrite::Unknown));
            }
        }
        for (var, known) in knowns {
            self.insert_written(var, known)
        }
    }

    /// Emit pending operations in the order and grouping specified in `to_emit`.
    fn emit_structured(&mut self, to_emit: Vec<SmallVec<(isize, Expr<C>), 1>>) {
        for calcs in to_emit {
            for (_, expr) in &calcs {
                for referenced in expr.variables() {
                    self.read(referenced);
                }
            }
            self.written_calcs(calcs.iter().map(|(i, v)| (*i, v)));
            self.insts.push(Instr::Calc { calcs });
        }
    }

    /// Emit the pending operations for the given variable `var`. All pending
    /// operations depending on `var` will also be emitted.
    fn emit(&mut self, var: isize) {
        if self.pending.contains_key(&var) {
            let to_emit = self.gather_for_emit(&[var]);
            self.emit_structured(to_emit);
        }
    }

    /// Mark the value of the variable `var` as clobbered from now on. This also
    /// removes any pending operation for this variable and emits all pending
    /// operations that require `var`.
    fn clobber(&mut self, var: isize, maybe: bool) {
        if !maybe {
            self.remove_pending(var);
        }
        let to_emit = self.gather_for_emit(&[var]);
        self.emit_structured(to_emit);
        self.insert_written(
            var,
            if maybe {
                OptWrite::Maybe
            } else {
                OptWrite::Unknown
            },
        );
    }

    /// After an uncertain move, all previously written are invalidated.
    fn uncertain_shift(&mut self) {
        self.parent = OptParent::Unknown;
        self.sub_shift = true;
        self.written.clear();
    }

    /// Record that the given variable has been read at this time.
    fn read(&mut self, var: isize) {
        if let None | Some(OptWrite::Maybe) = self.written.get(&var) {
            self.reads.insert(var);
        }
    }

    /// Get a hash set of all variables which have been read by this block, or
    /// for which there are operations pending that would read the variable if
    /// these operations will be emitted. Note that this ignores reads for pending
    /// operations that are reading the variable being assigned by the operation.
    fn possible_reads(&self) -> HashSet<isize> {
        self.reads
            .iter()
            .copied()
            .chain(
                self.pending
                    .iter()
                    .flat_map(|(&k, vs)| vs.variables().filter(move |&v| v != k)),
            )
            .collect()
    }

    /// Resolve all constants in the expression `expr`.
    fn reduce_const(&self, expr: Expr<C>, constant: &HashSet<isize>) -> Expr<C> {
        if expr.variables().any(|i| constant.contains(&i)) {
            expr.symb_evaluate(|i| {
                if constant.contains(&i) {
                    if let Some(c) = self.get_constant(i) {
                        return Some(Expr::val(c));
                    }
                }
                Some(Expr::var(i))
            })
            .unwrap()
        } else {
            expr
        }
    }

    /// Evaluate the expression `expr` based on the currently written operations.
    fn eval_written(&self, expr: impl Into<Expr<C>> + AsRef<Expr<C>>) -> Option<Expr<C>> {
        if expr
            .as_ref()
            .variables()
            .any(|x| self.written.contains_key(&x))
        {
            expr.as_ref().symb_evaluate(|i| self.get_written(i))
        } else {
            Some(expr.into())
        }
    }

    /// Evaluate the expression `expr` based on the currently pending operations.
    fn eval_pending(&self, shift: isize, expr: impl Into<Expr<C>> + AsRef<Expr<C>>) -> Expr<C> {
        if expr.as_ref().variables().any(|x| {
            self.pending.contains_key(&(x + shift))
                || self.get_written_constant(x + shift).is_some()
        }) {
            expr.as_ref()
                .symb_evaluate(|x| Some(self.get_pending(x + shift)))
                .unwrap()
        } else if shift != 0 {
            let mut res = expr.into();
            for var in res.variables_mut() {
                *var += shift;
            }
            res
        } else {
            expr.into()
        }
    }

    /// Return true if the currently written values of the two expressions are
    /// always the same. If equivalence is not guaranteed, false will be returned.
    fn compare_parent(
        &self,
        a: impl AsRef<Expr<C>> + Into<Expr<C>>,
        b: impl AsRef<Expr<C>> + Into<Expr<C>>,
    ) -> bool {
        if a.as_ref() == b.as_ref() {
            true
        } else if a
            .as_ref()
            .variables()
            .chain(b.as_ref().variables())
            .all(|x| self.can_ask_parent_for(x))
        {
            if let OptParent::Zero = self.parent {
                a.as_ref().constant_part() == b.as_ref().constant_part()
            } else if let OptParent::Parent(parent) = self.parent {
                parent.compare(a, b)
            } else {
                false
            }
        } else {
            false
        }
    }

    /// Return true if the currently written values of the two expressions are
    /// always the same. If equivalence is not guaranteed, false will be returned.
    /// This is the same as [`Self::compare_written`] but without inspecting the parent.
    fn compare_written_no_parent(
        &self,
        a: impl AsRef<Expr<C>> + Into<Expr<C>>,
        b: impl AsRef<Expr<C>> + Into<Expr<C>>,
    ) -> bool {
        if a.as_ref() == b.as_ref() {
            true
        } else {
            let a = self.eval_written(a);
            let b = self.eval_written(b);
            a.is_some() && a == b
        }
    }

    /// Return true if the currently written values of the two expressions are
    /// always the same. If equivalence is not guaranteed, false will be returned.
    fn compare_written(
        &self,
        a: impl AsRef<Expr<C>> + Into<Expr<C>>,
        b: impl AsRef<Expr<C>> + Into<Expr<C>>,
    ) -> bool {
        if a.as_ref() == b.as_ref() {
            true
        } else {
            let a = self.eval_written(a);
            let b = self.eval_written(b);
            a.is_some() && b.is_some() && self.compare_parent(a.unwrap(), b.unwrap())
        }
    }

    /// Return true if the values of the two expressions are always the same if
    /// evaluated given the current state. If equivalence is not guaranteed,
    /// false will be returned.
    fn compare(
        &self,
        a: impl AsRef<Expr<C>> + Into<Expr<C>>,
        b: impl AsRef<Expr<C>> + Into<Expr<C>>,
    ) -> bool {
        if a.as_ref() == b.as_ref() {
            true
        } else {
            let a = self.eval_pending(0, a);
            let b = self.eval_pending(0, b);
            self.compare_written(a, b)
        }
    }

    /// Analyze how often the loop with the given state will be executed given
    /// it is run with the current written and pending operations in mind.
    fn analyze_loop(&self, sub: &OptRebuild<C>, cond: isize, is_loop: bool) -> OptLoop<C> {
        let initial_cond = self.get_constant(cond);
        let at_least_once = self.is_non_zero(cond);
        if initial_cond == Some(C::ZERO) {
            OptLoop::expr(Expr::val(C::ZERO))
        } else if sub.no_return {
            OptLoop::no_return(at_least_once)
        } else if !is_loop {
            OptLoop::at_most_once(at_least_once)
        } else if let Some(stored_cond) = sub.get_constant(cond + sub.shift - self.shift) {
            if stored_cond == C::ZERO {
                OptLoop::at_most_once(at_least_once)
            } else {
                OptLoop::infinite(at_least_once)
            }
        } else if sub.sub_shift {
            OptLoop::unknown(at_least_once)
        } else if let Some(expr) = sub.get(cond + sub.shift - self.shift) {
            if let Some(inc) = expr.const_inc_of(cond) {
                if let Some(m) = initial_cond {
                    if let Some(n) = m.wrapping_div(inc.wrapping_neg()) {
                        OptLoop::expr(Expr::val(n))
                    } else {
                        OptLoop::infinite(at_least_once)
                    }
                } else {
                    if let Some(inv) = inc.wrapping_neg().wrapping_inv() {
                        OptLoop::expr(Expr::val(inv).mul(Expr::var(cond)))
                    } else if inc == C::ZERO {
                        OptLoop::infinite(at_least_once)
                    } else {
                        OptLoop::unknown(at_least_once)
                    }
                }
            } else if expr.identity() == Some(cond) {
                OptLoop::infinite(at_least_once)
            } else {
                OptLoop::unknown(at_least_once)
            }
        } else {
            OptLoop::unknown(at_least_once)
        }
    }

    /// Split a pending action into an operation that runs inside the loop, and
    /// an operation that runs before or after the loop.
    fn loop_motion(
        &self,
        var: isize,
        pending: Expr<C>,
        complete: bool,
        reads: &HashSet<isize>,
        constant: &HashSet<isize>,
        linear: &HashMap<isize, Expr<C>>,
        other_pending: &HashSet<isize>,
        loop_anal: &OptLoop<C>,
    ) -> [Option<Expr<C>>; 3] {
        if constant.contains(&var) && complete {
            return [None, None, None];
        }
        let pending = self.reduce_const(pending, constant);
        let used_vars = pending.variables().collect::<HashSet<_>>();
        if !reads.contains(&var) || loop_anal.at_most_once {
            if used_vars
                .iter()
                .all(|x| !other_pending.contains(x) || constant.contains(x))
            {
                return [None, None, Some(pending)];
            }
        }
        if !reads.contains(&var) {
            if complete {
                if let Some(expr) = &loop_anal.expr {
                    if let Some((inc, mul)) = pending.prod_inc_of(var) {
                        if mul == C::ONE {
                            let (constant, other, linears) = inc.split_along(constant, linear);
                            let mut before = expr.mul(constant);
                            let mut after = other;
                            let expr_neg_one = expr.add(Expr::val(C::NEG_ONE));
                            for (initial, increment) in linears {
                                if let Some(inc) = increment.half() {
                                    before = expr
                                        .mul(initial)
                                        .add(before.add(expr.mul(expr_neg_one.mul(inc))));
                                } else if let Some(inc) = expr.half() {
                                    before = expr
                                        .mul(initial)
                                        .add(before.add(expr_neg_one.mul(increment.mul(inc))));
                                } else if let Some(inc) = expr_neg_one.half() {
                                    before = expr
                                        .mul(initial)
                                        .add(before.add(expr.mul(increment.mul(inc))));
                                } else {
                                    after = after.add(initial);
                                }
                            }
                            return [
                                Some(Expr::var(var).add(before)),
                                Some(Expr::var(var).add(after)),
                                None,
                            ];
                        } else if let Some(c) = expr.constant() {
                            if inc.is_zero() {
                                return [
                                    Some(Expr::val(mul.wrapping_pow(c)).mul(Expr::var(var))),
                                    None,
                                    None,
                                ];
                            } else if inc.variables().all(|x| constant.contains(&x)) {
                                if let Some(m) = mul
                                    .wrapping_pow(c)
                                    .wrapping_mul(mul)
                                    .wrapping_add(C::NEG_ONE)
                                    .wrapping_div(mul.wrapping_add(C::NEG_ONE))
                                {
                                    return [
                                        Some(
                                            Expr::val(mul.wrapping_pow(c))
                                                .mul(Expr::var(var))
                                                .add(Expr::val(m).mul(inc)),
                                        ),
                                        None,
                                        None,
                                    ];
                                }
                            }
                        }
                    }
                }
            }
        }
        return [None, Some(pending), None];
    }

    /// Emit a loop if necessary, otherwise either inline or perform a load.
    fn loop_inside_if(
        &mut self,
        sub_state: OptRebuild<C>,
        cond: isize,
        loop_anal: OptLoop<C>,
        after: Vec<(isize, Expr<C>)>,
        constant: &HashSet<isize>,
    ) {
        if loop_anal.at_most_once {
            self.inline(sub_state);
        } else if loop_anal.finite
            && sub_state.shift == self.shift
            && sub_state.insts.is_empty()
            && sub_state.pending.len() == 1
            && sub_state.pending.contains_key(&cond)
        {
            self.perform_all(0, &[(cond, Expr::val(C::ZERO))]);
        } else {
            self.loop_or_if(sub_state, cond, true, loop_anal, &constant);
        }
        self.perform_all(0, &after);
    }

    /// Inline the given `sub_state` into this state.
    fn inline(&mut self, mut sub_state: OptRebuild<C>) {
        if sub_state.sub_shift {
            for var in self.pending(&self) {
                self.emit(var);
            }
            self.uncertain_shift();
        } else {
            for var in sub_state.reads(&self) {
                self.emit(var);
                self.read(var);
            }
        }
        let mut clobbered = Vec::new();
        for (&var, kind) in &sub_state.written {
            if let OptWrite::Maybe = kind {
                clobbered.push((var, true));
            } else {
                self.remove_pending(var);
                clobbered.push((var, false));
            }
        }
        clobbered.sort();
        for (var, maybe) in clobbered {
            self.clobber(var, maybe);
        }
        self.insts.append(&mut sub_state.insts);
        self.written_calcs(sub_state.written.into_iter().filter_map(|(v, w)| {
            if let OptWrite::Known(w) = w {
                Some((v, w))
            } else {
                None
            }
        }));
        if sub_state.no_return {
            self.no_return = true;
        } else {
            self.perform_all(0, &sub_state.pending.into_iter().collect::<Vec<_>>());
            self.shift = sub_state.shift;
        }
        self.sub_anal.append(&mut sub_state.sub_anal);
    }

    /// Emit a loop or if for the given `sub_state` inside this state.
    fn loop_or_if(
        &mut self,
        mut sub_state: OptRebuild<C>,
        cond: isize,
        is_loop: bool,
        loop_anal: OptLoop<C>,
        constant: &HashSet<isize>,
    ) {
        if !sub_state.no_return {
            for var in sub_state.pending(&sub_state) {
                sub_state.emit(var);
            }
        }
        let mut clobbered = HashSet::new();
        let has_shift = sub_state.sub_shift || sub_state.shift != self.shift;
        if has_shift {
            for var in self.pending(&self) {
                self.emit(var);
            }
            self.uncertain_shift();
        } else {
            sub_state.reads.insert(cond);
            let sub_reads = sub_state.reads(&self);
            for var in sub_reads {
                self.emit(var);
                self.read(var);
            }
            for (&var, _) in &sub_state.written {
                if !constant.contains(&var) {
                    clobbered.insert(var);
                }
            }
            if !loop_anal.no_effect {
                let mut clobber = Vec::new();
                for (&var, kind) in &sub_state.written {
                    if !constant.contains(&var) {
                        if matches!(kind, OptWrite::Maybe) || !loop_anal.at_least_once {
                            clobber.push((var, true));
                        } else {
                            self.remove_pending(var);
                            clobber.push((var, false));
                        }
                    }
                }
                clobber.sort();
                for (var, maybe) in clobber {
                    self.clobber(var, maybe);
                }
            }
            if let Some(OptWrite::Known(expr)) = sub_state.written.get(&cond) {
                if expr.constant() == Some(C::ZERO) {
                    self.insert_written(cond, OptWrite::Known(Expr::val(C::ZERO)));
                }
            }
        }
        let block = Block {
            shift: sub_state.shift - self.shift,
            insts: sub_state.insts,
        };
        if is_loop {
            self.insts.push(Instr::Loop {
                cond,
                block,
                once: loop_anal.at_least_once,
            });
            self.insert_written(cond, OptWrite::Known(Expr::val(C::ZERO)));
        } else {
            self.insts.push(Instr::If { cond, block });
        }
        if loop_anal.no_continue {
            self.no_return = true;
        }
        self.sub_anal.push(OptAnalysis {
            loop_anal,
            has_shift,
            reads: sub_state.reads,
            clobbered,
            sub_blocks: sub_state.sub_anal,
        });
    }

    /// Compute which of the given variables will stay constant at every execution
    /// of the loop, and will have the same value as at the beginning of the loop.
    /// This does not mean that the variable does not change inside the loop,
    /// only that at is will have the same value before the loop, after each
    /// iteration, and at each iteration before the still pending operations.
    fn constants_among(
        &self,
        sub_state: &OptRebuild<C>,
        vars: impl Iterator<Item = isize>,
    ) -> HashSet<isize> {
        fn check_constant<F, I>(
            var: isize,
            iter: F,
            constant: &mut HashSet<isize>,
            dependents: &mut HashMap<isize, Vec<isize>>,
            depends_on: &mut HashMap<isize, usize>,
        ) where
            F: Fn() -> I,
            I: Iterator<Item = isize>,
        {
            if iter().all(|x| x == var || constant.contains(&x)) {
                constant.insert(var);
            } else {
                let mut cnt = 0;
                for v in iter().filter(|&x| x != var) {
                    dependents.entry(v).or_insert(Vec::new()).push(var);
                    cnt += 1;
                }
                depends_on.insert(var, cnt);
            }
        }
        let mut constant = HashSet::new();
        let mut dependents = HashMap::new();
        let mut depends_on = HashMap::new();
        for var in vars {
            if let Some(write) = sub_state.written.get(&var) {
                if let OptWrite::Known(written) = write {
                    if self.compare(Expr::var(var), written) {
                        if let Some(pending) = sub_state.pending.get(&var) {
                            if self.compare(Expr::var(var), pending) {
                                check_constant(
                                    var,
                                    || written.variables().chain(pending.variables()),
                                    &mut constant,
                                    &mut dependents,
                                    &mut depends_on,
                                );
                            }
                        } else {
                            check_constant(
                                var,
                                || written.variables(),
                                &mut constant,
                                &mut dependents,
                                &mut depends_on,
                            );
                        }
                    }
                }
            } else if let Some(pending) = sub_state.pending.get(&var) {
                if self.compare(Expr::var(var), pending) {
                    check_constant(
                        var,
                        || pending.variables(),
                        &mut constant,
                        &mut dependents,
                        &mut depends_on,
                    );
                }
            } else {
                constant.insert(var);
            }
        }
        let mut stack = Vec::with_capacity(constant.len());
        stack.extend(constant.iter().copied());
        while let Some(c) = stack.pop() {
            if let Some(deps) = dependents.remove(&c) {
                for dep in deps {
                    let v = depends_on.get_mut(&dep).unwrap();
                    *v -= 1;
                    if *v == 0 {
                        stack.push(dep);
                        constant.insert(dep);
                    }
                }
            }
        }
        return constant;
    }

    /// Find the variables that only increment by an expression using only
    /// constants in their operation and return that increment.
    fn linear_among(
        &self,
        sub_state: &OptRebuild<C>,
        constant: &HashSet<isize>,
        vars: impl Iterator<Item = isize>,
    ) -> HashMap<isize, Expr<C>> {
        let mut linear = HashMap::new();
        for var in vars {
            if let Some(complete) = sub_state.get(var) {
                if let Some(inc) = complete.inc_of(var) {
                    if inc.variables().all(|x| constant.contains(&x)) {
                        linear.insert(var, inc);
                    }
                }
            }
        }
        return linear;
    }

    /// Get a sorted list of all variables with pending operations.
    fn pending(&self, sort_using: &Self) -> Vec<isize> {
        let mut vars = self.pending.keys().copied().collect::<Vec<_>>();
        vars.sort_by_key(|x| {
            if let Some(p) = sort_using.pending.get(x) {
                (p.add_count(), *x)
            } else {
                (0, *x)
            }
        });
        return vars;
    }

    /// Get a sorted list of all variables which have been read by this block.
    fn reads(&self, sort_using: &Self) -> Vec<isize> {
        let mut vars = self.reads.iter().copied().collect::<Vec<_>>();
        vars.sort_by_key(|x| {
            if let Some(p) = sort_using.pending.get(x) {
                (p.add_count(), *x)
            } else {
                (0, *x)
            }
        });
        return vars;
    }
}

impl<'a, C: CellType> OptRebuild<'a, C> {
    /// Create new (empty) rebuild state.
    fn new(
        shift: isize,
        cond: Option<isize>,
        parent: OptParent<'a, C>,
        anal: Option<OptAnalysis<C>>,
    ) -> Self {
        OptRebuild {
            parent,
            anal,
            shift,
            cond,
            sub_shift: false,
            no_return: false,
            reads: HashSet::new(),
            written: HashMap::new(),
            insts: Vec::new(),
            pending: HashMap::new(),
            reverse: HashMap::new(),
            sub_anal: Vec::new(),
        }
    }

    /// Transmute this state into one that has forgotten its parent.
    fn forget_parent(mut self) -> OptRebuild<'static, C> {
        self.parent = OptParent::Unknown;
        // Safety: We replace the only field bound by a lifetime.
        unsafe { mem::transmute(self) }
    }

    /// Perform the rebuilding steps with the given `block` and `shift` and return
    /// the state after the block, without emitting the final pending operations.
    fn rebuild_block(&mut self, block: &Block<C>) {
        if let Some(anal) = &mut self.anal {
            anal.sub_blocks.reverse();
        }
        for instr in &block.insts {
            if self.no_return {
                return;
            }
            match instr {
                Instr::Output { src } => {
                    let src = *src + self.shift;
                    if let Some(src) = self.retarget_output(src) {
                        self.read(src);
                        self.insts.push(Instr::Output { src });
                    } else {
                        self.emit(src);
                        self.read(src);
                        self.insts.push(Instr::Output { src });
                    }
                }
                Instr::Input { dst } => {
                    let dst = *dst + self.shift;
                    self.clobber(dst, false);
                    self.insts.push(Instr::Input { dst });
                }
                Instr::Calc { calcs } => {
                    self.perform_all(self.shift, calcs);
                }
                Instr::Loop { cond, block, .. } | Instr::If { cond, block } => {
                    let cond = *cond + self.shift;
                    let is_loop = matches!(instr, Instr::Loop { .. });
                    let sub_anal = if let Some(anal) = &mut self.anal {
                        anal.sub_blocks.pop()
                    } else {
                        None
                    };
                    let mut sub_state =
                        OptRebuild::new(self.shift, Some(cond), OptParent::Parent(&self), sub_anal);
                    sub_state.rebuild_block(block);
                    let loop_anal = self.analyze_loop(&sub_state, cond, is_loop);
                    if !loop_anal.never {
                        let mut after = Vec::new();
                        let mut before = Vec::new();
                        let constant;
                        if sub_state.sub_shift || sub_state.shift != self.shift {
                            constant = HashSet::new();
                        } else {
                            let pending = sub_state.pending(&sub_state);
                            let mut possible_reads = sub_state.possible_reads();
                            possible_reads.insert(cond);
                            constant = self.constants_among(
                                &sub_state,
                                possible_reads.iter().chain(pending.iter()).copied(),
                            );
                            let linear = self.linear_among(
                                &sub_state,
                                &constant,
                                possible_reads.iter().chain(pending.iter()).copied(),
                            );
                            let mut to_perform = Vec::new();
                            let pending_set = pending
                                .iter()
                                .copied()
                                .filter(|x| !constant.contains(x))
                                .collect();
                            for var in pending {
                                let has_written = sub_state.written.contains_key(&var);
                                let pending = sub_state.remove_pending(var).unwrap();
                                let [b, d, a] = self.loop_motion(
                                    var,
                                    pending,
                                    !has_written,
                                    &possible_reads,
                                    &constant,
                                    &linear,
                                    &pending_set,
                                    &loop_anal,
                                );
                                if let Some(b) = b {
                                    before.push((var, b));
                                }
                                if let Some(d) = d {
                                    to_perform.push((var, d));
                                }
                                if !loop_anal.no_effect {
                                    if let Some(a) = a {
                                        after.push((var, a));
                                    }
                                }
                            }
                            sub_state.perform_all(0, &to_perform);
                        }
                        sub_state = sub_state.forget_parent();
                        self.perform_all(0, &before);
                        if loop_anal.at_least_once || (!loop_anal.at_most_once && after.is_empty())
                        {
                            self.loop_inside_if(sub_state, cond, loop_anal, after, &constant);
                        } else {
                            let mut if_state = OptRebuild::<C>::new(
                                self.shift,
                                Some(cond),
                                OptParent::Unknown,
                                None,
                            );
                            if_state.loop_inside_if(
                                sub_state,
                                cond,
                                loop_anal.to_at_least_once(),
                                after,
                                &constant,
                            );
                            self.loop_or_if(
                                if_state,
                                cond,
                                false,
                                loop_anal.to_at_most_once(),
                                &constant,
                            );
                        }
                    }
                }
            }
        }
        self.shift += block.shift;
    }
}

impl<'a, C: CellType> OptDseState<'a, C> {
    /// Create a new state for performing dead store elimination.
    fn new(shift: isize, parent: Option<&'a OptDseState<'a, C>>, anal: &'a OptAnalysis<C>) -> Self {
        OptDseState {
            parent,
            shift,
            had_shift: false,
            anal,
            reads: HashSet::new(),
            written: HashSet::new(),
        }
    }

    /// Register that a read has been encountered during the reverse scan.
    fn read(&mut self, var: isize) {
        self.written.remove(&var);
        self.reads.insert(var);
    }

    /// Register that a write has been encountered during the reverse scan.
    fn write(&mut self, var: isize) {
        self.reads.remove(&var);
        self.written.insert(var);
    }

    /// Return true only if the value of `var` is guaranteed to be written before
    /// the next possible read.
    fn will_be_overwritten(&self, var: isize) -> bool {
        if self.written.contains(&var) {
            true
        } else if self.reads.contains(&var) || self.had_shift {
            false
        } else if let Some(parent) = self.parent {
            if self.anal.loop_anal.at_most_once
                || (!self.anal.has_shift && !self.anal.reads.contains(&var))
            {
                parent.will_be_overwritten(var - self.shift)
            } else {
                false
            }
        } else {
            // NB: We assume that nothing runs after the end of the program.
            true
        }
    }

    /// Eliminate dead stores in the given block.
    fn eliminate_in_block(&mut self, block: &mut Block<C>) {
        let mut block_idx = self.anal.sub_blocks.len();
        for instr in block.insts.iter_mut().rev() {
            match instr {
                Instr::Output { src } => self.read(*src),
                Instr::Input { dst } => self.write(*dst),
                Instr::Calc { calcs } => {
                    let mut to_remove = HashSet::new();
                    for (var, _) in calcs.iter() {
                        if self.will_be_overwritten(*var) {
                            to_remove.insert(*var);
                        } else {
                            self.write(*var);
                        }
                    }
                    calcs.retain(|(x, _)| !to_remove.contains(x));
                    for (_, calc) in calcs {
                        for var in calc.variables() {
                            self.read(var);
                        }
                    }
                }
                Instr::Loop { cond, block, .. } | Instr::If { cond, block } => {
                    block_idx -= 1;
                    self.read(*cond);
                    let sub_anal = &self.anal.sub_blocks[block_idx];
                    let mut sub_state = OptDseState::new(block.shift, Some(self), sub_anal);
                    sub_state.eliminate_in_block(block);
                    let OptDseState { reads, written, .. } = sub_state;
                    if sub_anal.has_shift {
                        self.had_shift = true;
                        self.written.clear();
                        self.reads.clear();
                    }
                    if sub_anal.loop_anal.at_least_once {
                        for var in written {
                            self.write(var);
                        }
                    }
                    for var in reads {
                        self.read(var);
                    }
                    self.read(*cond);
                }
            }
        }
    }
}

impl<C: CellType> Program<C> {
    /// Perform one iteration of optimization and return the new program.
    fn optimize_once(&self, prev_anal: OptAnalysis<C>) -> (Self, OptAnalysis<C>) {
        let mut state = OptRebuild::new(0, None, OptParent::Zero, Some(prev_anal));
        state.rebuild_block(self);
        // NB: We assume that nothing runs after the end of the program.
        (
            Program {
                shift: 0,
                insts: state.insts,
            },
            OptAnalysis {
                loop_anal: OptLoop::at_most_once(true),
                has_shift: false,
                reads: state.reads,
                clobbered: HashSet::new(),
                sub_blocks: state.sub_anal,
            },
        )
    }

    /// Remove computations that will be overwritten in any case.
    fn dead_store_elimination(&mut self, anal: &OptAnalysis<C>) {
        let mut state = OptDseState::new(0, None, anal);
        state.eliminate_in_block(self);
    }

    /// Optimize the program, and return the optimized copy of the program.
    pub fn optimize(&self, level: u32) -> Self {
        if level != 0 {
            let mut anal = OptAnalysis {
                loop_anal: OptLoop::at_most_once(true),
                has_shift: false,
                reads: HashSet::new(),
                clobbered: HashSet::new(),
                sub_blocks: Vec::new(),
            };
            let mut prog;
            (prog, anal) = self.optimize_once(anal);
            for _ in 1..(level.min(3)) {
                prog.dead_store_elimination(&anal);
                (prog, anal) = prog.optimize_once(anal);
            }
            return prog;
        } else {
            self.clone()
        }
    }
}
