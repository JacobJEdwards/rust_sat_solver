use crate::sat::clause::Clause;
use crate::sat::cnf::CNF;
use crate::sat::literal::Literal;
use crate::sat::trail::{Reason, Trail};

#[derive(Debug)]
pub enum Conflict {
    Ground,
    Unit(Clause),
    Learned(usize, Clause),
    Restart(Clause),
}

fn idx_in(idx: usize, seen: &Vec<bool>) -> bool {
    seen[idx]
}

fn resolve(c: &mut Clause, o: &Clause, idx: usize, c_idx: usize, trail: &Trail, seen: &mut Vec<bool>, path_c: &mut usize, to_bump: &mut Vec<usize>) {
    c.remove_literal(c_idx);
    *path_c -= 1;
    seen[idx] = false;

    for &lit in o.iter() {
        if !idx_in(lit.variable(), &seen) {
            seen[lit.variable()] = true;
            to_bump.push(lit.variable());
            c.literals.push(lit);
            if trail.lit_to_level[lit.variable()] == trail.decision_level() {
                *path_c += 1;
            }
        }
    }
}

fn choose_literal(c: &Clause, trail: &Trail, i: &mut usize, seen: &Vec<bool>) -> Option<usize> {
    while *i > 0 {
        *i -= 1;
        if seen[trail.trail[*i].lit.variable()] {
            for k in 0..c.len() {
                if trail.trail[*i].lit.variable() == c[k].variable() {
                    return Some(k);
                }
            }
        }
    }
    None
}

pub fn analyse_conflict(cnf: &CNF, trail: &Trail, cref: usize) -> Conflict {
    let dl = trail.decision_level();
    let mut to_bump = Vec::new();
    let break_cond = if dl == 0 { 0} else {1};
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
        let c_idx = match choose_literal(&clause, trail, &mut i, &seen) {
            Some(c_idx) => c_idx,
            None => break
        };
        let ante = match trail.trail[i].reason {
            Reason::Long(ante) => cnf[ante].clone(),
            Reason::Unit(ante) => cnf[ante].clone(),
            _ => break
        };
        let idx = trail.trail[i].lit.variable();
        resolve(clause, &ante, idx, c_idx, trail, &mut seen, &mut path_c, &mut to_bump);
    }
    
    if clause.len() == 0 {
        Conflict::Ground
    } else if clause.len() == 1 {
        Conflict::Unit(clause.clone())
    } else {
        if path_c > break_cond {
            return Conflict::Restart(clause.clone());
        }
        let mut s_idx: usize = 0;
        for k in 0..clause.len() {
            if trail.lit_to_level[clause[k].variable()] == dl {
                s_idx = k;
                break;
            }
        }
        Conflict::Learned(s_idx, clause.clone())
    }
    
}