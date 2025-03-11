#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use crate::sat::trail::Reason;
use std::collections::VecDeque;

pub trait PropagationStructure {
    fn new(cnf: &Cnf) -> Self;
    fn push(&mut self, p: (Literal, Option<Reason>));
    fn pop(&mut self) -> Option<(Literal, Option<Reason>)>;
}

fn initial_propagation<T: FromIterator<(Literal, Option<Reason>)>>(cnf: &Cnf) -> T {
    cnf.iter()
        .filter(|c| c.is_unit())
        .map(|c| (c[0], Some(Reason::Unit(c[0].variable()))))
        .collect()
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Hash, PartialOrd, Ord)]
pub struct PropagationQueue(VecDeque<(Literal, Option<Reason>)>);


impl PropagationStructure for PropagationQueue {
    fn new(cnf: &Cnf) -> Self {
        Self(initial_propagation(cnf))
    }

    fn push(&mut self, p: (Literal, Option<Reason>)) {
        self.0.push_back(p);
    }

    fn pop(&mut self) -> Option<(Literal, Option<Reason>)> {
        self.0.pop_front()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Hash, PartialOrd, Ord)]
pub struct PropagationStack(Vec<(Literal, Option<Reason>)>);

impl PropagationStack {
    pub fn iter(&self) -> impl Iterator<Item = &(Literal, Option<Reason>)> {
        self.0.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut (Literal, Option<Reason>)> {
        self.0.iter_mut()
    }
}

impl PropagationStructure for PropagationStack {
    fn new(cnf: &Cnf) -> Self {
        Self(initial_propagation(cnf))
    }

    fn push(&mut self, p: (Literal, Option<Reason>)) {
        self.0.push(p);
    }

    fn pop(&mut self) -> Option<(Literal, Option<Reason>)> {
        self.0.pop()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::clause::Clause;

    #[test]
    fn test_propagation_queue() {
        let cnf = Cnf {
            clauses: vec![
                Clause::new(vec![Literal::new(1, false)]),
                Clause::new(vec![Literal::new(2, false)]),
                Clause::new(vec![Literal::new(3, false)]),
            ],
            num_vars: 3,
        };

        let mut q = PropagationQueue::new(&cnf);

        assert_eq!(q.pop(), Some((Literal::new(1, false), Some(Reason::Unit(1)))));
        assert_eq!(q.pop(), Some((Literal::new(2, false), Some(Reason::Unit(2)))));
        assert_eq!(q.pop(), Some((Literal::new(3, false), Some(Reason::Unit(3)))));
        assert_eq!(q.pop(), None);
    }

    #[test]
    fn test_propagation_stack() {
        let cnf = Cnf {
            clauses: vec![
                Clause::new(vec![Literal::new(1, false)]),
                Clause::new(vec![Literal::new(2, false)]),
                Clause::new(vec![Literal::new(3, false)]),
            ],
            num_vars: 3,
        };

        let mut q = PropagationStack::new(&cnf);

        assert_eq!(q.pop(), Some((Literal::new(3, false), Some(Reason::Unit(3)))));
        assert_eq!(q.pop(), Some((Literal::new(2, false), Some(Reason::Unit(2)))));
        assert_eq!(q.pop(), Some((Literal::new(1, false), Some(Reason::Unit(1)))));
        assert_eq!(q.pop(), None);
    }
}