use crate::sat::assignment::Assignment;
use crate::sat::cnf::CNF;
use crate::sat::literal::Literal;

#[derive(Debug, Clone, PartialEq, Eq, Default, Copy, Hash, PartialOrd, Ord)]
pub enum Reason {
    #[default]
    Decision,
    Unit(usize),
    Long(usize)
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Step {
    pub lit: Literal,
    pub decision_level: usize,
    pub reason: Reason,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Trail {
    pub trail: Vec<Step>,
    pub curr_idx: usize,
    pub lit_to_level: Vec<usize>,
}

impl Trail {
    pub fn decision_level(&self) -> usize {
        self.trail[self.curr_idx].decision_level
    }
    
    pub fn last(&self) -> Literal {
        self.trail[self.curr_idx].lit
    }
    
    pub fn len(&self) -> usize {
        self.trail.len()
    }
    
    pub fn iter(&self) -> impl Iterator<Item = &Step> {
        self.trail.iter()
    }
    
    pub fn new(cnf: &CNF) -> Self {
        Self {
            trail: Vec::with_capacity(cnf.num_vars + 1),
            curr_idx: 0,
            lit_to_level: vec![0; cnf.num_vars + 1],
        }
    }
    
    pub fn push(&mut self, lit: Literal, decision_level: usize, reason: Reason) {
        self.trail.push(Step { lit, decision_level, reason });
        self.lit_to_level[lit.variable()] = decision_level;
    }
    
    pub fn backstep(&mut self, a: &mut Assignment) {
        let mut i = self.trail.len() - 1;
        while self.trail[i].reason != Reason::Decision {
            let lit = self.trail[i].lit;
            a.unassign(lit.variable());
            i -= 1;
        }
        self.curr_idx = i;
        self.trail.truncate(i);
    }
    
    pub fn backstep_to(&mut self, a: &mut Assignment, level: usize) {
        let mut i = self.trail.len() - 1;
        while self.trail[i].decision_level > level {
            let lit = self.trail[i].lit;
            a.unassign(lit.variable());
            i -= 1;
        }
        self.curr_idx = i;
        self.trail.truncate(i);
    }
}