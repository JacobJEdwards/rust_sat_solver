use super::cnf;
use crate::sat::cnf::{is_negative, Variable};
use std::collections::hash_map::HashMap;
use std::collections::HashSet;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Assignment(HashMap<Variable, (bool, cnf::DecisionLevel, Option<cnf::Clause>)>);

pub type Solutions = Vec<i32>;

// impl Solutions {
//     pub fn iter(&self) -> impl Iterator<Item = &usize> {
//         self.0.iter()
//     }
// }
// 
// impl Solutions {
//     pub fn check(&self, i: usize) -> bool {
//         self.0.contains(&i)
//     }
// 
//     pub fn empty() -> Self {
//         Solutions(HashSet::new())
//     }
// }

impl Assignment {
    pub fn new() -> Self {
        Assignment(HashMap::with_hasher(Default::default()))
    }

    pub fn set(&mut self, i: usize, b: bool, dl: cnf::DecisionLevel, reason: Option<cnf::Clause>) {
        self.0.insert(i, (b, dl, reason));
    }

    pub fn get(&self, i: usize) -> Option<&(bool, cnf::DecisionLevel, Option<cnf::Clause>)> {
        self.0.get(&i)
    }

    pub fn unset(&mut self, i: usize) {
        self.0.remove(&i);
    }

    pub fn get_solutions(&self) -> Solutions {
        let positives = self
            .0
            .iter()
            .filter(|(_, (b, _, _))| *b)
            .map(|(i, _)| *i as i32)
            .collect::<Vec<_>>();
        positives
    }

    pub fn get_all_assigned(&self) -> Vec<usize> {
        self.0.keys().map(|x| *x).collect::<Vec<_>>()
    }

    pub fn var_value(&self, i: usize) -> Option<bool> {
        self.0.get(&i).map(|(b, _, _)| *b)
    }

    pub fn literal_value(&self, l: cnf::Literal) -> Option<bool> {
        let i = cnf::var_of_lit(l);
        let b = self.var_value(i)?;
        if is_negative(l) {
            Some(!b)
        } else {
            Some(b)
        }
    }
}
