//! Optimizer for the internal IR. Performs mostly constant propagation,
//! loop analysis, and dead code elimination.

use crate::{
    hasher::{HashMap, HashSet},
    smallvec::SmallVec,
    Block, CellType, Expr, Instr, Program,
};

/// A write can either be known, unknown. A write that is not guaranteed to happen
/// is encoded with [`OptWrite::Maybe`], while a write that is guaranteed to happen,
/// but for which we don't know the value is encoded with [`OptWrite::Unknown`].
enum OptWrite<C: CellType> {
    Known(Expr<C>),
    Unknown,
    Maybe,
}

/// State for rebuilding a single block. Includes both the already emitted instructions,
/// their effect, and all the pending operations.
struct OptRebuild<C: CellType> {
    shift: isize,
    cond: Option<isize>,
    sub_shift: bool,
    no_return: bool,
    reads: HashSet<isize>,
    written: HashMap<isize, OptWrite<C>>,
    insts: Vec<Instr<C>>,
    pending: HashMap<isize, Expr<C>>,
    reverse: HashMap<isize, HashSet<isize>>,
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

impl<C: CellType> OptLoop<C> {
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
}

impl<C: CellType> OptRebuild<C> {
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
        if expr.identity() != Some(var) {
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
            if expr.identity() != Some(var) {
                self.written.insert(var, OptWrite::Known(expr.normalize()));
            } else {
                self.written.remove(&var);
            }
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

    /// Get the combination of pending and written operations performed for the
    /// given variable since the start of the block, or [`None`] if unknown.
    fn get(&self, var: isize) -> Option<Expr<C>> {
        if let Some(expr) = self.pending.get(&var) {
            self.eval_written(expr)
        } else {
            self.get_written(var)
        }
    }

    /// If the variable `var` is known to have a constant value already written
    /// to it, return that value, otherwise return [`None`].
    fn get_written_constant(&self, var: isize) -> Option<C> {
        if let Some(OptWrite::Known(expr)) = self.written.get(&var) {
            expr.constant()
        } else {
            None
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
        if let Some(c) = self.get_constant(var) {
            c != C::ZERO
        } else if !self.sub_shift
            && !self.pending.contains_key(&var)
            && !self.written.contains_key(&var)
        {
            self.cond == Some(var)
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
        run: usize,
        depth: usize,
        visited: &mut HashMap<isize, (usize, usize)>,
        stack: &mut Vec<isize>,
        comps: &mut Vec<SmallVec<isize, 1>>,
    ) -> usize {
        visited.insert(var, (run, depth));
        let stack_len = stack.len();
        let mut low = depth;
        if let Some(next) = self.reverse.get(&var) {
            let mut next = next.iter().copied().collect::<Vec<_>>();
            next.sort();
            for n in next {
                if let Some((r, v)) = visited.get(&n) {
                    if *r == run {
                        low = low.min(*v);
                    }
                } else {
                    let reached = self.gather_to_emit_dfs(n, run, depth + 1, visited, stack, comps);
                    low = low.min(reached);
                }
            }
        }
        if self.pending.contains_key(&var) {
            stack.push(var);
        }
        if low == depth && stack.len() != stack_len {
            let mut new_comp = SmallVec::with_capacity(stack.len() - stack_len);
            while stack.len() != stack_len {
                new_comp.push(stack.pop().unwrap());
            }
            comps.push(new_comp);
        }
        return low;
    }

    /// Emitting a pending operation might necessitate either emitting or adjusting
    /// other pending operations. This function performs the necessary steps and
    /// returns the operations that must be performed grouped by, and in the order
    /// in which they must be emitted.
    fn gather_for_emit(&mut self, emit: &[isize]) -> Vec<SmallVec<isize, 1>> {
        let mut comps = Vec::new();
        if emit.iter().all(|var| !self.reverse.contains_key(var)) {
            // Optimize the common case where no one depends on anyone else.
            for &var in emit {
                if self.pending.contains_key(&var) {
                    comps.push(SmallVec::with(var));
                }
            }
        } else {
            let mut visited = HashMap::with_capacity(2 * emit.len());
            let mut stack = Vec::with_capacity(4);
            for (run, &var) in emit.iter().enumerate() {
                if !visited.contains_key(&var) {
                    self.gather_to_emit_dfs(var, run, 0, &mut visited, &mut stack, &mut comps);
                }
            }
        }
        return comps;
    }

    /// Record the execution of the given operations.
    fn written_calcs(&mut self, calcs: impl Iterator<Item = (isize, OptWrite<C>)>) {
        let mut knowns = SmallVec::<_, 1>::with_capacity(calcs.size_hint().0);
        for (var, calc) in calcs {
            if let OptWrite::Known(calc) = calc {
                if let Some(calc) = self.eval_written(calc) {
                    knowns.push((var, OptWrite::Known(calc)));
                } else {
                    knowns.push((var, OptWrite::Unknown));
                }
            } else {
                knowns.push((var, calc));
            }
        }
        for (var, known) in knowns {
            self.insert_written(var, known)
        }
    }

    /// Emit pending operations in the order and grouping specified in `to_emit`.
    fn emit_structured(&mut self, to_emit: Vec<SmallVec<isize, 1>>) {
        for vars in to_emit {
            let mut calcs = SmallVec::with_capacity(vars.len());
            for var in vars {
                if let Some(calc) = self.remove_pending(var) {
                    for referenced in calc.variables() {
                        self.read(referenced);
                    }
                    calcs.push((var, calc));
                }
            }
            self.written_calcs(calcs.iter().map(|(i, v)| (*i, OptWrite::Known(v.clone()))));
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
        self.sub_shift = true;
        self.written.clear();
    }

    /// Record that the given variable has been read at this time.
    fn read(&mut self, var: isize) {
        if let None | Some(OptWrite::Maybe) = self.written.get(&var) {
            self.reads.insert(var);
        }
    }

    /// Get a sorted list of all variables with pending operations.
    fn pending(&self) -> Vec<isize> {
        let mut vars = self.pending.keys().copied().collect::<Vec<_>>();
        vars.sort();
        return vars;
    }

    /// Get a sorted list of all variables which have been written by this block.
    fn writes(&self) -> Vec<isize> {
        let mut vars = self.written.keys().copied().collect::<Vec<_>>();
        vars.sort();
        return vars;
    }

    /// Get a sorted list of all variables which have been read by this block.
    fn reads(&self) -> Vec<isize> {
        let mut vars = self.reads.iter().copied().collect::<Vec<_>>();
        vars.sort();
        return vars;
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
            a.is_some() && a == b
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
    fn analyze_loop(&self, sub: &Self, cond: isize, is_loop: bool) -> OptLoop<C> {
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
        if !reads.contains(&var) {
            if complete {
                if let Some(expr) = &loop_anal.expr {
                    if let Some(inc) = pending.inc_of(var) {
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
                    }
                    if let Some(c) = expr.constant() {
                        if let Some(m) = pending.const_prod_of(var) {
                            return [
                                Some(Expr::val(m.wrapping_pow(c)).mul(Expr::var(var))),
                                None,
                                None,
                            ];
                        }
                    }
                }
            }
        }
        if !reads.contains(&var) || loop_anal.at_most_once {
            if used_vars.iter().all(|x| !other_pending.contains(x)) {
                return [None, None, Some(pending)];
            }
        }
        return [None, Some(pending), None];
    }

    /// Inline the given `sub_state` into this state.
    fn inline(&mut self, mut sub_state: Self) {
        if sub_state.sub_shift {
            for var in self.pending() {
                self.emit(var);
            }
            self.uncertain_shift();
        } else {
            for var in sub_state.reads() {
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
        self.written_calcs(sub_state.written.into_iter());
        if sub_state.no_return {
            self.no_return = true;
        } else {
            self.perform_all(0, &sub_state.pending.into_iter().collect::<Vec<_>>());
            self.shift = sub_state.shift;
        }
    }

    /// Emit a loop or if for the given `sub_state` inside this state.
    fn loop_or_if(
        &mut self,
        mut sub_state: Self,
        cond: isize,
        is_loop: bool,
        loop_anal: &OptLoop<C>,
    ) {
        if !sub_state.no_return {
            for var in sub_state.pending() {
                sub_state.emit(var);
            }
        }
        if sub_state.sub_shift || sub_state.shift != self.shift {
            for var in self.pending() {
                self.emit(var);
            }
            self.uncertain_shift();
        } else {
            sub_state.reads.insert(cond);
            let sub_reads = sub_state.reads();
            for var in sub_reads {
                self.emit(var);
                self.read(var);
            }
            if !loop_anal.no_effect {
                let sub_written = sub_state.writes();
                let constants = self.constants_among(&sub_state, sub_written.iter().copied());
                for var in sub_written {
                    if !constants.contains(&var) {
                        self.clobber(var, true);
                    }
                }
            }
            for (var, write) in sub_state.written {
                if let OptWrite::Known(expr) = write {
                    if var == cond && expr.constant() == Some(C::ZERO) {
                        self.insert_written(cond, OptWrite::Known(Expr::val(C::ZERO)));
                    }
                }
            }
        }
        let block = Block {
            shift: sub_state.shift - self.shift,
            insts: sub_state.insts,
        };
        if is_loop {
            self.insts.push(Instr::Loop { cond, block });
            self.insert_written(cond, OptWrite::Known(Expr::val(C::ZERO)));
        } else {
            self.insts.push(Instr::If { cond, block });
        }
        if loop_anal.no_continue {
            self.no_return = true;
        }
    }

    /// Compute which of the given variables will stay constant at every execution
    /// of the loop, and will have the same value as at the beginning of the loop.
    /// This does not mean that the variable does not change inside the loop,
    /// only that at is will have the same value before the loop, after each
    /// iteration, and at each iteration before the still pending operations.
    fn constants_among(
        &self,
        sub_state: &Self,
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
        sub_state: &Self,
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
}

impl<C: CellType> OptRebuild<C> {
    /// Create new (empty) rebuild state.
    fn new(shift: isize, cond: Option<isize>) -> Self {
        OptRebuild {
            shift,
            cond,
            sub_shift: false,
            no_return: false,
            reads: HashSet::new(),
            written: HashMap::new(),
            insts: Vec::new(),
            pending: HashMap::new(),
            reverse: HashMap::new(),
        }
    }

    /// Perform the rebuilding steps with the given `block` and `shift` and return
    /// the state after the block, without emitting the final pending operations.
    fn rebuild_block(&mut self, block: &Block<C>) {
        for instr in &block.insts {
            if self.no_return {
                return;
            }
            match instr {
                Instr::Output { src } => {
                    let src = *src + self.shift;
                    self.emit(src);
                    self.read(src);
                    self.insts.push(Instr::Output { src });
                }
                Instr::Input { dst } => {
                    let dst = *dst + self.shift;
                    self.clobber(dst, false);
                    self.insts.push(Instr::Input { dst });
                }
                Instr::Calc { calcs } => {
                    self.perform_all(self.shift, calcs);
                }
                Instr::Loop { cond, block } | Instr::If { cond, block } => {
                    let cond = *cond + self.shift;
                    let is_loop = matches!(instr, Instr::Loop { .. });
                    let mut sub_state = OptRebuild::new(self.shift, Some(cond));
                    sub_state.rebuild_block(block);
                    let loop_anal = self.analyze_loop(&sub_state, cond, is_loop);
                    if !loop_anal.never {
                        let mut after = Vec::new();
                        if !sub_state.sub_shift && sub_state.shift == self.shift {
                            let pending = sub_state.pending();
                            let mut possible_reads = sub_state.possible_reads();
                            possible_reads.insert(cond);
                            let constant = self.constants_among(
                                &sub_state,
                                possible_reads.iter().chain(pending.iter()).copied(),
                            );
                            let linear = self.linear_among(
                                &sub_state,
                                &constant,
                                possible_reads.iter().chain(pending.iter()).copied(),
                            );
                            let mut before = Vec::new();
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
                            self.perform_all(0, &before);
                            sub_state.perform_all(0, &to_perform);
                        }
                        let mut if_state = OptRebuild::<C>::new(self.shift, Some(cond));
                        if loop_anal.at_most_once {
                            if_state.inline(sub_state);
                        } else if loop_anal.finite
                            && sub_state.shift == self.shift
                            && sub_state.insts.is_empty()
                            && sub_state.pending.len() == 1
                            && sub_state.pending.contains_key(&cond)
                        {
                            if_state.perform_all(0, &[(cond, Expr::val(C::ZERO))]);
                        } else {
                            if_state.loop_or_if(sub_state, cond, true, &loop_anal);
                        }
                        if_state.perform_all(0, &after);
                        if loop_anal.at_least_once || (!loop_anal.at_most_once && after.is_empty())
                        {
                            self.inline(if_state);
                        } else if !if_state.insts.is_empty() || !if_state.pending.is_empty() {
                            self.loop_or_if(if_state, cond, false, &loop_anal);
                        }
                    }
                }
            }
        }
        self.shift += block.shift;
    }
}

impl<C: CellType> Program<C> {
    /// Perform one iteration of optimization and return the new program.
    fn optimize_once(&self) -> Self {
        let mut state = OptRebuild::new(0, None);
        state.rebuild_block(self);
        for var in state.pending() {
            state.emit(var);
        }
        Program {
            shift: state.shift,
            insts: state.insts,
        }
    }

    /// Optimize the program, and return the optimized copy of the program.
    pub fn optimize(&self, level: u32) -> Self {
        if level != 0 {
            let mut result = self.optimize_once();
            for _ in 1..level {
                result = result.optimize_once();
            }
            return result;
        } else {
            self.clone()
        }
    }
}
