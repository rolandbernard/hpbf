use std::{
    collections::{HashMap, HashSet},
    mem,
};

use crate::{Block, CellType, Expr, Instr, Program};

/// State for rebuilding a single block. Includes both the already emitted instructions,
/// their effect, and all the pending operations.
struct OptRebuild<C: CellType> {
    shift: isize,
    sub_shift: bool,
    reads: HashSet<isize>,
    known: HashMap<isize, Option<Expr<C>>>,
    insts: Vec<Instr<C>>,
    pending: HashMap<isize, Expr<C>>,
    reverse: HashMap<isize, HashSet<isize>>,
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
            for v in expr.variables() {
                let users = self.reverse.entry(v).or_insert(HashSet::new());
                users.insert(var);
            }
            self.pending.insert(var, expr);
        }
    }

    /// Mark the value of the variable `var` as clobbered from now on. This also
    /// removes any pending operation for this variable.
    fn clobber(&mut self, var: isize) {
        self.remove_pending(var);
        self.known.insert(var, None);
    }

    /// Get the pending operation for the given variable. If there is no operation
    /// pending for var, return the identity expression.
    fn get_pending(&self, var: isize) -> Expr<C> {
        if let Some(expr) = self.pending.get(&var) {
            expr.clone()
        } else {
            Expr::var(var)
        }
    }

    /// Get the current operation that has been performed to the variable `var`
    /// relative to the start of the block. If the result would depend on a
    /// clobbered value, return [`None`].
    fn get_known(&self, var: isize) -> Option<Expr<C>> {
        if let Some(expr) = self.known.get(&var) {
            expr.clone()
        } else {
            Some(Expr::var(var))
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

    /// Emitting a pending operation might necessitate either emitting or adjusting
    /// other pending operations. This function performs the necessary steps and
    /// returns the operations that must be performed grouped by, and in the order
    /// in which they must be emitted.
    fn gather_for_emit(&mut self, var: isize) -> Vec<Vec<isize>> {
        fn dfs<C: CellType>(
            state: &OptRebuild<C>,
            var: isize,
            depth: usize,
            index: &mut HashMap<isize, usize>,
            comp: &mut Vec<isize>,
            comps: &mut Vec<Vec<isize>>,
        ) -> usize {
            index.insert(var, depth);
            let mut min = depth + 1;
            if let Some(next) = state.reverse.get(&var) {
                for &n in next {
                    if let Some(i) = index.get(&n) {
                        min = min.min(*i);
                    } else {
                        min = min.min(dfs(state, n, depth + 1, index, comp, comps));
                    }
                }
            }
            if min > depth && !comp.is_empty() {
                let mut new_comp = Vec::new();
                mem::swap(&mut new_comp, comp);
                comps.push(new_comp);
            }
            comp.push(var);
            return min;
        }
        let mut components = Vec::new();
        if self.pending.contains_key(&var) {
            let mut index = HashMap::new();
            let mut component = Vec::new();
            dfs(self, var, 0, &mut index, &mut component, &mut components);
            if !component.is_empty() {
                components.push(component);
            }
        }
        return components;
    }

    /// Emit the pending operations for the given variable `var`.
    fn emit(&mut self, var: isize) {
        let to_emit = self.gather_for_emit(var);
        for vars in to_emit {
            let mut calcs = Vec::with_capacity(vars.len());
            let mut knowns = Vec::with_capacity(vars.len());
            for var in vars {
                if let Some(calc) = self.remove_pending(var) {
                    for referenced in calc.variables() {
                        self.read(referenced);
                    }
                    let known = calc.symb_evaluate(|i| self.get_known(i));
                    calcs.push((var, calc));
                    knowns.push((var, known));
                }
            }
            for (var, known) in knowns {
                self.known.insert(var, known);
            }
            self.insts.push(Instr::Calc { calcs });
        }
    }

    /// Record that the given variable has been read at this time.
    fn read(&mut self, var: isize) {
        if !self.known.contains_key(&var) {
            self.reads.insert(var);
        }
    }

    /// Get a sorted list of all variables with pending operations.
    fn pending(&self) -> Vec<isize> {
        let mut vars = self.pending.keys().copied().collect::<Vec<_>>();
        vars.sort();
        return vars;
    }
}

impl<C: CellType> OptRebuild<C> {
    /// Perform the rebuilding steps with the given `block` and `shift` and return
    /// the state after the block, without emitting the final pending operations.
    fn rebuild_block(block: &Block<C>, shift: isize) -> Self {
        let mut state = OptRebuild {
            shift,
            sub_shift: false,
            reads: HashSet::new(),
            known: HashMap::new(),
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
                    state.insts.push(Instr::Input { dst });
                    state.clobber(dst);
                }
                Instr::Calc { calcs } => {
                    state.perform_all(state.shift, calcs);
                }
                Instr::Loop { cond, block } | Instr::If { cond, block } => {
                    let cond = *cond + state.shift;
                    let is_loop = matches!(instr, Instr::Loop { .. });
                    for var in state.pending() {
                        state.emit(var);
                    }
                    let mut sub_state = OptRebuild::rebuild_block(block, state.shift);
                    if sub_state.sub_shift || sub_state.shift != state.shift {
                        state.sub_shift = true;
                    }
                    for var in sub_state.pending() {
                        sub_state.emit(var);
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
        state.shift += block.shift;
        return state;
    }
}

impl<C: CellType> Program<C> {
    /// Optimize the program, and return the optimized copy of the program.
    pub fn optimize(&self) -> Self {
        let mut state = OptRebuild::rebuild_block(self, 0);
        for var in state.pending() {
            state.emit(var);
        }
        Program {
            shift: state.shift,
            insts: state.insts,
        }
    }
}
