use crate::sat::assignment::Assignment;
use crate::sat::clause::Clause;
use crate::sat::clause_storage::LiteralStorage;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use crate::sat::propagation::Propagator;
use crate::sat::trail::Trail;
use rustc_hash::{FxHashMap, FxHashSet};
use std::fmt::Debug;

pub trait ClauseManagement<L: Literal, S: LiteralStorage<L>>: Clone + Debug {
    fn new(clauses: &[Clause<L, S>]) -> Self;
    fn on_conflict(&mut self, cnf: &mut Cnf<L, S>);
    fn should_clean_db(&self) -> bool;
    fn clean_clause_db<P: Propagator<L, S, A>, A: Assignment>(
        &mut self,
        cnf: &mut Cnf<L, S>,
        trail: &mut Trail<L, S>,
        propagator: &mut P,
        assignment: &mut A,
    );
    fn bump_involved_clause_activities(&mut self, cnf: &mut Cnf<L, S>, c_ref: usize);
}

#[derive(Debug, Clone, Default, PartialEq)]
pub struct LbdClauseManagement<L: Literal, S: LiteralStorage<L>, const N: usize> {
    interval: usize,
    conflicts_since_last_cleanup: usize,

    candidates: Vec<(usize, u32, f64)>,
    indices_to_remove: FxHashSet<usize>,
    new_learnt_clauses: Vec<Clause<L, S>>,
    old_to_new_idx_map: FxHashMap<usize, usize>,
}

impl<L: Literal, S: LiteralStorage<L>, const N: usize> ClauseManagement<L, S>
    for LbdClauseManagement<L, S, N>
{
    fn new(clauses: &[Clause<L, S>]) -> Self {
        let mut candidates = Vec::with_capacity(clauses.len());
        candidates.reserve(clauses.len());

        let mut indices_to_remove = FxHashSet::default();
        indices_to_remove.reserve(clauses.len());

        let mut new_learnt_clauses = Vec::with_capacity(clauses.len());
        new_learnt_clauses.reserve(clauses.len());

        let mut old_to_new_idx_map = FxHashMap::default();
        old_to_new_idx_map.reserve(clauses.len());

        Self {
            interval: N,
            conflicts_since_last_cleanup: 0,
            candidates,
            indices_to_remove,
            new_learnt_clauses,
            old_to_new_idx_map,
        }
    }

    fn on_conflict(&mut self, cnf: &mut Cnf<L, S>) {
        self.conflicts_since_last_cleanup += 1;
        self.decay_clause_activities(cnf);
    }

    fn should_clean_db(&self) -> bool {
        self.conflicts_since_last_cleanup >= self.interval
    }

    fn clean_clause_db<P: Propagator<L, S, A>, A: Assignment>(
        &mut self,
        cnf: &mut Cnf<L, S>,
        trail: &mut Trail<L, S>,
        propagator: &mut P,
        _: &mut A,
    ) {
        let learnt_start_idx = cnf.non_learnt_idx;
        if cnf.len() <= learnt_start_idx {
            return;
        }

        self.candidates.clear();

        let locked_clauses = trail.get_locked_clauses();

        for idx in learnt_start_idx..cnf.len() {
            if !locked_clauses.contains(&idx) {
                let clause = &cnf[idx];
                self.candidates.push((idx, clause.lbd, clause.activity()));
            }
        }

        let candidates = &mut self.candidates;

        if candidates.is_empty() {
            return;
        }

        let num_candidates = candidates.len();
        let num_to_remove = num_candidates / 2;

        if num_to_remove == 0 {
            return;
        }

        let comparison = |a: &(usize, u32, f64), b: &(usize, u32, f64)| {
            let (_, lbd_a, act_a) = a;
            let (_, lbd_b, act_b) = b;

            let keep_a = *lbd_a <= 2;
            let keep_b = *lbd_b <= 2;

            if keep_a && !keep_b {
                return std::cmp::Ordering::Greater;
            }
            if !keep_a && keep_b {
                return std::cmp::Ordering::Less;
            }

            match lbd_b.cmp(lbd_a) {
                std::cmp::Ordering::Equal => act_a
                    .partial_cmp(act_b)
                    .unwrap_or(std::cmp::Ordering::Equal),
                other => other,
            }
        };

        candidates.select_nth_unstable_by(num_to_remove, comparison);

        self.indices_to_remove.clear();
        for (idx, _, _) in &candidates[..num_to_remove] {
            self.indices_to_remove.insert(*idx);
        }

        let indices_to_remove = &self.indices_to_remove;

        self.new_learnt_clauses.clear();
        self.old_to_new_idx_map.clear();

        let mut current_new_idx = learnt_start_idx;
        for old_idx in learnt_start_idx..cnf.len() {
            if !indices_to_remove.contains(&old_idx) {
                self.new_learnt_clauses.push(cnf[old_idx].clone());
                self.old_to_new_idx_map.insert(old_idx, current_new_idx);
                current_new_idx += 1;
            }
        }

        let new_total_len = learnt_start_idx + self.new_learnt_clauses.len();

        cnf.clauses.truncate(learnt_start_idx);
        cnf.clauses.append(&mut self.new_learnt_clauses);

        trail.remap_clause_indices(&self.old_to_new_idx_map);

        propagator.cleanup_learnt(learnt_start_idx);
        for new_idx in learnt_start_idx..new_total_len {
            propagator.add_clause(&cnf[new_idx], new_idx);
        }

        self.conflicts_since_last_cleanup = 0;
    }

    fn bump_involved_clause_activities(&mut self, cnf: &mut Cnf<L, S>, c_ref: usize) {
        let clause = &mut cnf[c_ref];
        clause.bump_activity(1.0);
    }
}

impl<L: Literal, S: LiteralStorage<L>, const N: usize> LbdClauseManagement<L, S, N> {
    fn decay_clause_activities(&mut self, cnf: &mut Cnf<L, S>) {
        for clause in &mut cnf.clauses[cnf.non_learnt_idx..] {
            clause.decay_activity(0.95);
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq)]
pub struct NoClauseManagement<L: Literal, S: LiteralStorage<L>> {
    _phantom: std::marker::PhantomData<(L, S)>,
}

impl<L: Literal, S: LiteralStorage<L>> ClauseManagement<L, S> for NoClauseManagement<L, S> {
    fn new(_clauses: &[Clause<L, S>]) -> Self {
        Self {
            _phantom: std::marker::PhantomData,
        }
    }

    fn on_conflict(&mut self, _cnf: &mut Cnf<L, S>) {}

    fn should_clean_db(&self) -> bool {
        false
    }

    fn clean_clause_db<P: Propagator<L, S, A>, A: Assignment>(
        &mut self,
        _cnf: &mut Cnf<L, S>,
        _trail: &mut Trail<L, S>,
        _propagator: &mut P,
        _assignment: &mut A,
    ) {
    }

    fn bump_involved_clause_activities(&mut self, _cnf: &mut Cnf<L, S>, _c_ref: usize) {}
}
