use crate::sat::assignment::{Assignment, Solutions};
use crate::sat::cnf::Cnf;

pub trait Solver {
    fn new(cnf: Cnf) -> Self;
    fn solve(&mut self) -> Option<Solutions>;
    fn solutions(&self) -> Solutions;
    fn assignment(&self) -> &impl Assignment;
}
