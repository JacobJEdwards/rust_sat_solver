#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]

use crate::sat::assignment::Assignment;
use crate::sat::clause::Clause;
use crate::sat::cnf::Cnf;
use crate::sat::literal::{Literal, Variable};
use crate::sat::trail::{Reason, Trail};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub enum Conflict<T: Literal> {
    #[default]
    Ground,
    Unit(Clause<T>),           // (clause)
    Learned(usize, Clause<T>), // (s_idx, clause)
    Restart(Clause<T>),        // (clause)
}

pub struct Analyser<T: Literal> {
    seen: Vec<bool>,
    path_c: usize,
    to_bump: Vec<Variable>,
    data: std::marker::PhantomData<T>
}

impl <T: Literal> Analyser <T> {
    fn new(num_vars: usize) -> Self {
        Self {
            seen: vec![false; num_vars],
            path_c: 0,
            to_bump: Vec::new(),
            data: std::marker::PhantomData
        }
    }

    fn resolve(
        &mut self,
        c: &mut Clause<T>,
        o: &Clause<T>,
        assignment: &impl Assignment,
        idx: Variable,
        c_idx: usize,
        trail: &Trail<T>,
    ) {
        c.remove_literal(c_idx);
        self.path_c -= 1;
        self.seen[idx as usize] = false;

        for &lit in o.iter() {
            if !self.seen[lit.variable() as usize] && assignment.literal_value(lit) == Some(false) {
                self.seen[lit.variable() as usize] = true;
                self.to_bump.push(lit.variable());
                c.push(lit);

                if trail.lit_to_level[lit.variable() as usize] >= trail.decision_level() {
                    self.path_c += 1;
                }
            }
        }
    }

    fn choose_literal(&self, c: &Clause<T>, trail: &Trail<T>, i: &mut usize) -> Option<usize> {
        while *i > 0 {
            *i -= 1;
            if self.seen[trail[*i].lit.variable() as usize] {
                for k in 0..c.len() {
                    if trail[*i].lit.variable() == c[k].variable() {
                        return Some(k);
                    }
                }
            }
        }
        None
    }

    fn analyse_conflict(
        &mut self,
        cnf: &Cnf<T>,
        trail: &Trail<T>,
        assignment: &impl Assignment,
        cref: usize,
    ) -> (Conflict<T>, Vec<Variable>) {
        let dl = trail.decision_level();

        let mut i = trail.len();
        let clause = &mut cnf[cref].clone();

        for &lit in clause.iter() {
            self.seen[lit.variable() as usize] = true;
            self.to_bump.push(lit.variable());
            if trail.lit_to_level[lit.variable() as usize] >= dl {
                self.path_c += 1;
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

        #[cfg(debug_assertions)]
        for lit in clause.iter() {
            assert_eq!(
                assignment.literal_value(*lit),
                Some(false),
                "Learned clause contains non-falsified literal: {lit:?}"
            );
        }

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
                if trail.lit_to_level[var as usize] == dl {
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

    pub fn analyse(
        cnf: &Cnf<T>,
        trail: &Trail<T>,
        assignment: &impl Assignment,
        cref: usize,
    ) -> (Conflict<T>, Vec<Variable>) {
        let mut analyser = Self::new(cnf.num_vars);
        analyser.analyse_conflict(cnf, trail, assignment, cref)
    }
}
