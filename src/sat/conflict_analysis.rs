#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]

use crate::sat::clause::Clause;
use crate::sat::cnf::Cnf;
use crate::sat::trail::{Reason, Trail};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub enum Conflict {
    #[default]
    Ground,
    Unit(Clause),
    Learned(usize, Clause),
    Restart(Clause),
}

fn resolve(
    c: &mut Clause,
    o: &Clause,
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

    for &lit in o.iter().skip(1) {
        if !seen[lit.variable()] {
            seen[lit.variable()] = true;
            to_bump.push(lit.variable());
            c.literals.push(lit);
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

#[must_use] pub fn analyse_conflict(cnf: &Cnf, trail: &Trail, cref: usize) -> (Conflict, Vec<usize>) {
    let dl = trail.decision_level();
    
    let mut to_bump = Vec::new();
    let break_cond = usize::from(dl != 0);
    let mut path_c: usize = 0;
    let mut seen = vec![false; cnf.num_vars + 1];
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
            idx,
            c_idx,
            trail,
            &mut seen,
            &mut path_c,
            &mut to_bump,
        );
    }

    if clause.is_empty() {
        (Conflict::Ground, to_bump)
    } else if clause.len() == 1 {
        (Conflict::Unit(clause.clone()), to_bump)
    } else {
        if path_c > break_cond {
            return (Conflict::Restart(clause.clone()), to_bump);
        }
        let mut s_idx: usize = 0;
        for k in 0..clause.len() {
            if trail.lit_to_level[clause[k].variable()] == dl {
                s_idx = k;
                break;
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
        let conflict = analyse_conflict(&cnf, &trail, cref);
    }
}