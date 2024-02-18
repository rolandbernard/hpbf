use std::collections::{HashMap, HashSet};

use crate::{Block, CellType, Expr, Instr, Program};

/// State for rebuilding a single block. Includes both the already emitted instructions,
/// their effect, and all the pending operations.
struct OptRebuild<C: CellType> {
    shift: isize,
    cond: Option<isize>,
    sub_shift: bool,
    no_return: bool,
    reads: HashSet<isize>,
    written: HashMap<isize, Option<Expr<C>>>,
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
    no_return: bool,
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
            no_return: false,
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
            no_return: true,
            no_continue: true,
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
            no_return: false,
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
                no_return: false,
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
            no_return: false,
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
                let users = self.reverse.get_mut(&v).unwrap();
                users.remove(&var);
                if users.is_empty() {
                    self.reverse.remove(&v);
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
            for v in expr.variables() {
                let users = self.reverse.entry(v).or_insert(HashSet::new());
                users.insert(var);
            }
            self.pending.insert(var, expr);
        }
    }

    /// Remove an entry from the set of known cells. This really only to be used
    /// right before inserting a new value.
    fn remove_written(&mut self, var: isize) -> Option<Expr<C>> {
        if let Some(Some(expr)) = self.written.insert(var, None) {
            Some(expr)
        } else {
            None
        }
    }

    /// Insert a new known cell operation.
    fn insert_written(&mut self, var: isize, val: Option<Expr<C>>) {
        self.remove_written(var);
        if let Some(expr) = val {
            if expr.identity() != Some(var) {
                self.written.insert(var, Some(expr));
            }
        } else {
            self.written.insert(var, None);
        }
    }

    /// Get the current operation that has been performed to the variable `var`
    /// relative to the start of the block. If the result would depend on a
    /// clobbered value, return [`None`].
    fn get_written(&self, var: isize) -> Option<Expr<C>> {
        if let Some(expr) = self.written.get(&var) {
            expr.clone()
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
            expr.symb_evaluate(|i| self.get_written(i))
        } else {
            self.get_written(var)
        }
    }

    /// If the variable `var` is known to have a constant value already written
    /// to it, return that value, otherwise return [`None`].
    fn get_written_constant(&self, var: isize) -> Option<C> {
        if let Some(Some(expr)) = self.written.get(&var) {
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
        let mut exprs = Vec::new();
        for (var, expr) in calcs {
            let pending = expr
                .symb_evaluate(|i| Some(self.get_pending(i + shift)))
                .unwrap();
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
        comps: &mut Vec<Vec<isize>>,
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
        if low == depth {
            let mut new_comp = Vec::new();
            while stack.len() != stack_len {
                new_comp.push(stack.pop().unwrap());
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
    fn gather_for_emit(&mut self, emit: &[isize]) -> Vec<Vec<isize>> {
        let mut visited = HashMap::new();
        let mut stack = Vec::new();
        let mut comps = Vec::new();
        for (run, &var) in emit.iter().enumerate() {
            if !visited.contains_key(&var) {
                self.gather_to_emit_dfs(var, run, 0, &mut visited, &mut stack, &mut comps);
            }
        }
        return comps;
    }

    /// Record the execution of the given operations.
    fn written_calcs<'a>(&mut self, calcs: impl Iterator<Item = (isize, Option<&'a Expr<C>>)>)
    where
        C: 'a,
    {
        let mut knowns = Vec::new();
        for (var, calc) in calcs {
            if let Some(calc) = calc {
                knowns.push((var, calc.symb_evaluate(|i| self.get_written(i))));
            } else {
                knowns.push((var, None));
            }
        }
        for (var, known) in knowns {
            self.remove_pending(var);
            self.insert_written(var, known)
        }
    }

    /// Emit pending operations in the order and grouping specified in `to_emit`.
    fn emit_structured(&mut self, to_emit: Vec<Vec<isize>>) {
        for vars in to_emit {
            let mut calcs = Vec::with_capacity(vars.len());
            for var in vars {
                if let Some(calc) = self.remove_pending(var) {
                    for referenced in calc.variables() {
                        self.read(referenced);
                    }
                    calcs.push((var, calc));
                }
            }
            self.written_calcs(calcs.iter().map(|(i, v)| (*i, Some(v))));
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
    fn clobber(&mut self, var: isize) {
        self.remove_pending(var);
        let to_emit = self.gather_for_emit(&[var]);
        self.emit_structured(to_emit);
        self.insert_written(var, None);
    }

    /// After an uncertain move, all previously written are invalidated.
    fn uncertain_shift(&mut self) {
        self.sub_shift = true;
        self.written.clear();
    }

    /// Record that the given variable has been read at this time.
    fn read(&mut self, var: isize) {
        if !self.written.contains_key(&var) {
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

    /// Get a sorted list of all variables which have been read by this block, or
    /// for which there are operations pending that would read the variable if
    /// these operations will be emitted. Note that this ignores reads for pending
    /// operations that are reading the variable being assigned by the operation.
    fn possible_reads(&self) -> Vec<isize> {
        let mut vars = self
            .reads
            .iter()
            .copied()
            .chain(
                self.pending
                    .iter()
                    .flat_map(|(&k, vs)| vs.variables().filter(move |&v| v != k)),
            )
            .collect::<Vec<_>>();
        vars.sort();
        return vars;
    }

    /// Return true if the values of the two expressions are always the same if
    /// evaluated given the current state. If equivalence is not guaranteed,
    /// false will be returned.
    fn compare(&self, a: Expr<C>, b: Expr<C>) -> bool {
        if a == b {
            return true;
        }
        let a = a.symb_evaluate(|i| Some(self.get_pending(i))).unwrap();
        let b = b.symb_evaluate(|i| Some(self.get_pending(i))).unwrap();
        if a == b {
            return true;
        }
        let a = a.symb_evaluate(|i| self.get_written(i));
        let b = b.symb_evaluate(|i| self.get_written(i));
        if a.is_some() && a == b {
            return true;
        }
        return false;
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
        } else if let Some(stored_cond) = sub.get_constant(cond + sub.shift) {
            if stored_cond == C::ZERO {
                OptLoop::at_most_once(at_least_once)
            } else {
                OptLoop::infinite(at_least_once)
            }
        } else if sub.sub_shift {
            OptLoop::unknown(at_least_once)
        } else if let Some(expr) = sub.get(cond + sub.shift) {
            if let Some(inc) = expr.const_inc_of(cond) {
                if let Some(m) = initial_cond {
                    if let Some(n) = m.wrapping_div(inc.wrapping_neg()) {
                        OptLoop::expr(Expr::val(n))
                    } else {
                        OptLoop::infinite(at_least_once)
                    }
                } else {
                    if let Some(inv) = inc.wrapping_neg().wrapping_inv() {
                        OptLoop::expr(Expr::val(inv).mul(&Expr::var(cond)))
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
}

impl<C: CellType> OptRebuild<C> {
    /// Perform the rebuilding steps with the given `block` and `shift` and return
    /// the state after the block, without emitting the final pending operations.
    fn rebuild_block(block: &Block<C>, shift: isize, cond: Option<isize>) -> Self {
        let mut state = OptRebuild {
            shift,
            cond,
            sub_shift: false,
            no_return: false,
            reads: HashSet::new(),
            written: HashMap::new(),
            insts: Vec::new(),
            pending: HashMap::new(),
            reverse: HashMap::new(),
        };
        for instr in &block.insts {
            match instr {
                Instr::Output { src } => {
                    let src = *src + state.shift;
                    state.emit(src);
                    state.read(src);
                    state.insts.push(Instr::Output { src });
                }
                Instr::Input { dst } => {
                    let dst = *dst + state.shift;
                    state.clobber(dst);
                    state.insts.push(Instr::Input { dst });
                }
                Instr::Calc { calcs } => {
                    state.perform_all(state.shift, calcs);
                }
                Instr::Loop { cond, block } | Instr::If { cond, block } => {
                    let cond = *cond + state.shift;
                    let is_loop = matches!(instr, Instr::Loop { .. });
                    let mut sub_state = OptRebuild::rebuild_block(block, state.shift, Some(cond));
                    let loop_anal = state.analyze_loop(&sub_state, cond, is_loop);
                    if !loop_anal.never {
                        if loop_anal.at_least_once && loop_anal.at_most_once {
                            if sub_state.sub_shift || sub_state.shift != state.shift {
                                for var in state.pending() {
                                    state.emit(var);
                                }
                                state.uncertain_shift();
                            } else {
                                for var in sub_state.reads() {
                                    state.emit(var);
                                    state.read(var);
                                }
                            }
                            state.insts.append(&mut sub_state.insts);
                            state.written_calcs(
                                sub_state.written.iter().map(|(i, v)| (*i, v.as_ref())),
                            );
                            state.perform_all(
                                state.shift,
                                &sub_state.pending.into_iter().collect::<Vec<_>>(),
                            );
                            state.shift = sub_state.shift;
                        } else {
                            for var in sub_state.pending() {
                                sub_state.emit(var);
                            }
                            if sub_state.sub_shift || sub_state.shift != state.shift {
                                for var in state.pending() {
                                    state.emit(var);
                                }
                                state.uncertain_shift();
                            } else {
                                sub_state.reads.insert(cond);
                                let sub_reads = sub_state.reads();
                                for var in sub_reads {
                                    state.emit(var);
                                    state.read(var);
                                }
                                let sub_written = sub_state.writes();
                                for var in sub_written {
                                    state.emit(var);
                                    state.clobber(var);
                                }
                            }
                            let block = Block {
                                shift: sub_state.shift - state.shift,
                                insts: sub_state.insts,
                            };
                            if is_loop {
                                state.insts.push(Instr::Loop { cond, block });
                            } else {
                                state.insts.push(Instr::If { cond, block });
                            }
                        }
                    }
                }
            }
        }
        state.shift += block.shift;
        return state;
    }
}

impl<C: CellType> Program<C> {
    /// Optimize the program, and return the optimized copy of the program.
    pub fn optimize(&self) -> Self {
        let mut state = OptRebuild::rebuild_block(self, 0, None);
        for var in state.pending() {
            state.emit(var);
        }
        Program {
            shift: state.shift,
            insts: state.insts,
        }
    }
}
