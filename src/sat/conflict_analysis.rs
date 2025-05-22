#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
/// Defines functions related to conflict analysis


use crate::sat::assignment::Assignment;
use crate::sat::clause::Clause;
use crate::sat::clause_storage::LiteralStorage;
use crate::sat::cnf::Cnf;
use crate::sat::literal::{Literal, Variable};
use crate::sat::trail::{Reason, Trail};
use bit_vec::BitVec;
use smallvec::SmallVec;

/// The type of a conflict
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub enum Conflict<T: Literal, S: LiteralStorage<T>> {
    #[default]
    Ground,
    /// The clause is the learnt clause
    Unit(Clause<T, S>),           // (clause)
    /// The usize is the position of the asserting lit. 
    /// Maybe unneeded, could just put it in first place.
    Learned(usize, Clause<T, S>), // (s_idx, clause)
    Restart(Clause<T, S>),        // (clause)
}

/// Defines methods for conflict analysis
/// A struct is used instead of free functions in order to reuse allocations.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Analyser<T: Literal, S: LiteralStorage<T>, const N: usize = 12> {
    seen: BitVec,
    path_c: usize,
    to_bump: SmallVec<[T; N]>,
    data: std::marker::PhantomData<*const (T, S)>,

    pub count: usize,
}

impl<T: Literal, S: LiteralStorage<T>, const N: usize> Analyser<T, S, N> {
    /// Initialise the analysis
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            seen: BitVec::from_elem(num_vars, false),
            path_c: 0,
            to_bump: SmallVec::with_capacity(12),
            data: std::marker::PhantomData,
            count: 0,
        }
    }

    /// Check whether a literal has been seen
    /// Unsafe for a tiny speed up, the idx is guarranteed
    fn is_seen(&self, idx: Variable) -> bool {
        unsafe { self.seen.get_unchecked(idx as usize) }
    }

    /// Make a variable as seen
    fn set_seen(&mut self, idx: Variable) {
        unsafe {
            *self.seen.get_unchecked_mut(idx as usize) = true;
        }
    }

    /// Mark a variable as not having been seen.
    fn unset_seen(&mut self, idx: Variable) {
        unsafe {
            *self.seen.get_unchecked_mut(idx as usize) = false;
        }
    }

    /// Apply the resolution rule.
    fn resolve(
        &mut self,
        c: &mut Clause<T, S>, /// conflict clause
        o: &Clause<T, S>, /// other clause
        assignment: &impl Assignment,
        idx: Variable,
        c_idx: usize,
        trail: &Trail<T, S>,
    ) {
        c.remove_literal(c_idx);
        self.path_c -= 1;
        self.unset_seen(idx);

        for &lit in o.iter() {
            let var = lit.variable();
            if !self.is_seen(var) && assignment.literal_value(lit) == Some(false) {
                self.set_seen(var);
                self.to_bump.push(lit);
                c.push(lit);

                if trail.level(var) >= trail.decision_level() {
                    self.path_c = self.path_c.wrapping_add(1);
                }
            }
        }
    }

    /// Choose the literal to add to the learnt clause
    fn choose_literal(
        &self,
        c: &Clause<T, S>,
        trail: &Trail<T, S>,
        i: &mut usize,
    ) -> Option<usize> {
        while *i > 0 {
            *i -= 1;
            let var = trail[*i].lit.variable();

            if self.is_seen(var) {
                for k in 0..c.len() {
                    if var == c[k].variable() {
                        return Some(k);
                    }
                }
            }
        }
        None
    }

    /// The main conflict analysis
    pub(crate) fn analyse_conflict(
        &mut self,
        cnf: &Cnf<T, S>,
        trail: &Trail<T, S>,
        assignment: &impl Assignment,
        cref: usize, /// The clause index
    ) -> (Conflict<T, S>, SmallVec<[T; N]>) {
        self.count = self.count.wrapping_add(1);

        let dl = trail.decision_level();

        let mut i = trail.len();
        let clause = &mut cnf[cref].clone();

        for &lit in clause.iter() {
            let var = lit.variable();
            self.set_seen(var);
            self.to_bump.push(lit);
            if trail.level(var) >= dl {
                self.path_c = self.path_c.wrapping_add(1);
            }
        }

        while self.path_c > usize::from(dl != 0) {
            let Some(c_idx) = self.choose_literal(clause, trail, &mut i) else {
                break;
            };

            let ante = match trail[i].reason {
                Reason::Clause(c_idx) | Reason::Unit(c_idx) => cnf[c_idx].clone(),
                Reason::Decision => break,
            };

            let idx = trail[i].lit.variable();

            self.resolve(clause, &ante, assignment, idx, c_idx, trail);
        }

        // was having problems with an incorrectly formed learnt clause
        debug_assert!(clause
            .iter()
            .all(|lit| assignment.literal_value(*lit) == Some(false)));

        if clause.is_empty() {
            (Conflict::Ground, self.to_bump.clone())
        } else if clause.is_unit() {
            (Conflict::Unit(clause.clone()), self.to_bump.clone())
        } else {
            if self.path_c > usize::from(dl != 0) {
                return (Conflict::Restart(clause.clone()), self.to_bump.clone());
            }
            let mut max_pos = 0;
            let mut s_idx: usize = 0;

            for k in 0..clause.len() {
                let var = clause[k].variable();
                if trail.level(var) == dl {
                    let pos = trail.lit_to_pos[var as usize];
                    if pos > max_pos {
                        max_pos = pos;
                        s_idx = k;
                    }
                }
            }
            (
                Conflict::Learned(s_idx, clause.clone()),
                self.to_bump.clone(),
            )
        }
    }

    /// reset between conflicts
    pub(crate) fn reset(&mut self) {
        self.seen.clear();
        self.path_c = 0;
        self.to_bump.clear();
    }
}
