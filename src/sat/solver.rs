use crate::sat::assignment::Solutions;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;

pub trait Solver<L: Literal> {
    fn new(cnf: Cnf<L>) -> Self;
    fn solve(&mut self) -> Option<Solutions>;
    fn solutions(&self) -> Solutions;
}
