// #![warn(
//     clippy::all,
//     clippy::restriction,
//     clippy::pedantic,
//     clippy::nursery,
//     clippy::cargo,
// )]
// 
use crate::sat::cnf::CNF;
use crate::sat::literal::Literal;
use std::collections::VecDeque;
use crate::sat::trail::Reason;

#[derive(Debug, Clone, PartialEq, Eq, Default, Hash, PartialOrd, Ord)]
pub struct PropagationQueue(VecDeque<(Literal, Option<Reason>)>);

impl PropagationQueue {
    pub fn new(cnf: &CNF) -> Self {
        let q = cnf
            .iter()
            .filter(|c| c.is_unit())
            .map(|c| (c[0], Some(Reason::Unit(c[0].variable()))))
            .collect();

        Self(q)
    }

    pub fn push(&mut self, p: (Literal, Option<Reason>)) {
        self.0.push_back(p);
    }

    pub fn pop(&mut self) -> Option<(Literal, Option<Reason>)> {
        self.0.pop_front()
    }
    
    pub fn iter(&self) -> impl Iterator<Item = &(Literal, Option<Reason>)> {
        self.0.iter()
    }
    
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut (Literal, Option<Reason>)> {
        self.0.iter_mut()
    }
}
