#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]

use crate::sat::assignment::Assignment;
use crate::sat::clause::Clause;
use crate::sat::cnf::Cnf;
use crate::sat::cdcl::State;
use crate::sat::trail::{Reason, Trail};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub enum Conflict {
    #[default]
    Ground,
    Unit(Clause),           // (clause)
    Learned(usize, Clause), // (s_idx, clause)
    Restart(Clause),        // (clause)
}

pub struct Analyser {
    seen: Vec<bool>,
    path_c: usize,
    to_bump: Vec<usize>,
}

impl Analyser {
    fn new(num_vars: usize) -> Self {
        Self {
            seen: vec![false; num_vars],
            path_c: 0,
            to_bump: Vec::new(),
        }
    }
    
    fn resolve(
        &mut self,
        c: &mut Clause,
        o: &Clause,
        assignment: &impl Assignment,
        idx: usize,
        c_idx: usize,
        trail: &Trail,
    ) {
        c.remove_literal(c_idx);
        self.path_c -= 1;
        self.seen[idx] = false;

        for &lit in o.iter() {
            if !self.seen[lit.variable()] && assignment.literal_value(lit) == Some(false) {
                self.seen[lit.variable()] = true;
                self.to_bump.push(lit.variable());
                c.push(lit);

                if trail.lit_to_level[lit.variable()] >= trail.decision_level() {
                    self.path_c += 1;
                }
            }
        }
    }
    
    fn choose_literal(&mut self, c: &Clause, trail: &Trail, i: &mut usize) -> Option<usize> {
        while *i > 0 {
            *i -= 1;
            if self.seen[trail[*i].lit.variable()] {
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
        cnf: &Cnf,
        trail: &Trail,
        assignment: &impl Assignment,
        cref: usize,
    ) -> (Conflict, Vec<usize>) {
        let dl = trail.decision_level();
    
        let mut i = trail.len();
        let clause = &mut cnf[cref].clone();
    
        for &lit in clause.iter() {
            self.seen[lit.variable()] = true;
            self.to_bump.push(lit.variable());
            if trail.lit_to_level[lit.variable()] >= dl {
                self.path_c += 1;
            }
        }
    
        while self.path_c > usize::from(dl != 0) {
            let Some(c_idx) = self.choose_literal(clause, trail, &mut i) else {
                break;
            };
    
            let ante = match trail[i].reason {
                Reason::Long(ante) | Reason::Unit(ante) => cnf[ante].clone(),
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
                if trail.lit_to_level[var] == dl {
                    let pos = trail.lit_to_pos[var];
                    if pos > max_pos {
                        max_pos = pos;
                        s_idx = k;
                    }
                }
            }
            (Conflict::Learned(s_idx, clause.clone()), self.to_bump.clone())
        }
    }
    
    
    pub fn analyse(
        cnf: &Cnf,
        trail: &Trail,
        assignment: &impl Assignment,
        cref: usize,
    ) -> (Conflict, Vec<usize>) {
        let mut analyser = Analyser::new(cnf.num_vars);
        analyser.analyse_conflict(cnf, trail, assignment, cref)
    }
}

fn resolve(
    c: &mut Clause,
    o: &Clause,
    assignment: &impl Assignment,
    idx: usize,
    c_idx: usize,
    trail: &Trail,
    seen: &mut [bool],
    path_c: &mut usize,
    to_bump: &mut Vec<usize>,
) {
    c.remove_literal(c_idx);
    *path_c -= 1;
    seen[idx] = false;

    for &lit in o.iter() {
        if !seen[lit.variable()] && assignment.literal_value(lit) == Some(false) {
            seen[lit.variable()] = true;
            to_bump.push(lit.variable());
            c.push(lit);

            if trail.lit_to_level[lit.variable()] >= trail.decision_level() {
                *path_c += 1;
            }
        }
    }
}

fn choose_literal(c: &Clause, trail: &Trail, i: &mut usize, seen: &[bool]) -> Option<usize> {
    while *i > 0 {
        *i -= 1;
        if seen[trail[*i].lit.variable()] {
            for k in 0..c.len() {
                if trail[*i].lit.variable() == c[k].variable() {
                    return Some(k);
                }
            }
        }
    }
    None
}

#[must_use]
pub fn analyse_conflict(
    cnf: &Cnf,
    trail: &Trail,
    assignment: &impl Assignment,
    cref: usize,
) -> (Conflict, Vec<usize>) {
    let dl = trail.decision_level();

    let mut to_bump = Vec::new();
    let break_cond = usize::from(dl != 0);
    let mut path_c: usize = 0;
    let mut seen = vec![false; cnf.num_vars];
    let mut i = trail.len();
    let clause = &mut cnf[cref].clone();

    for &lit in clause.iter() {
        seen[lit.variable()] = true;
        to_bump.push(lit.variable());
        if trail.lit_to_level[lit.variable()] >= dl {
            path_c += 1;
        }
    }

    while path_c > break_cond {
        let Some(c_idx) = choose_literal(clause, trail, &mut i, &seen) else {
            break;
        };

        let ante = match trail[i].reason {
            Reason::Long(ante) | Reason::Unit(ante) => cnf[ante].clone(),
            Reason::Decision => break,
        };

        let idx = trail[i].lit.variable();

        resolve(
            clause,
            &ante,
            assignment,
            idx,
            c_idx,
            trail,
            &mut seen,
            &mut path_c,
            &mut to_bump,
        );
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
        (Conflict::Ground, to_bump)
    } else if clause.is_unit() {
        (Conflict::Unit(clause.clone()), to_bump)
    } else {
        if path_c > break_cond {
            return (Conflict::Restart(clause.clone()), to_bump);
        }
        let mut max_pos = 0;
        let mut s_idx: usize = 0;

        for k in 0..clause.len() {
            let var = clause[k].variable();
            if trail.lit_to_level[var] == dl {
                let pos = trail.lit_to_pos[var];
                if pos > max_pos {
                    max_pos = pos;
                    s_idx = k;
                }
            }
        }
        (Conflict::Learned(s_idx, clause.clone()), to_bump)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_analyse_conflict() {
        let cnf = Cnf::new(vec![vec![1, 2, 3], vec![4, 5, 6]]);
        let trail = Trail::new(&cnf);
        let cref = 0;
    }
}
