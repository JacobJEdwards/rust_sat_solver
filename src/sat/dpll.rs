use crate::sat::assignment::Assignment;
use crate::sat::cnf;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use crate::sat::propagation::Propagator;
use crate::sat::solver::{DefaultConfig, SolutionStats, Solutions, Solver, SolverConfig};
use crate::sat::trail::Trail;
use crate::sat::variable_selection::VariableSelection;

#[derive(Debug, Clone)]
pub struct Dpll<Config: SolverConfig + Clone = DefaultConfig> {
    pub trail: Trail<Config::Literal, Config::LiteralStorage>,
    pub assignment: Config::Assignment,
    pub decision_level: cnf::DecisionLevel,
    pub cnf: Cnf<Config::Literal, Config::LiteralStorage>,
    pub selector: Config::VariableSelector,
    pub propagator: Config::Propagator,
}

impl<Config: SolverConfig + Clone> Solver<Config> for Dpll<Config> {
    fn new(cnf: Cnf<Config::Literal, Config::LiteralStorage>) -> Self {
        let lits = &cnf.lits;
        let propagator = Propagator::new(&cnf);
        let assignment = Assignment::new(cnf.num_vars);
        let trail = Trail::new(&cnf);
        let selector = Config::VariableSelector::new(cnf.num_vars, lits, &cnf.clauses);

        Self {
            trail,
            assignment,
            decision_level: 0,
            cnf,
            selector,
            propagator,
        }
    }

    fn solve(&mut self) -> Option<Solutions> {
        self.propagate();

        if self.is_sat() {
            return Some(self.solutions());
        }

        if self.is_unsat() {
            return None;
        }

        let var = self.selector.pick(&self.assignment)?;

        self.decision_level = self.decision_level.wrapping_add(1);

        let mut true_branch = self.clone();
        let mut false_branch = self.clone();

        true_branch
            .assignment
            .assign(Config::Literal::new(var.variable(), true));
        false_branch
            .assignment
            .assign(Config::Literal::new(var.variable(), false));

        if let Some(solutions) = true_branch.solve() {
            return Some(solutions);
        }

        false_branch.solve()
    }

    fn solutions(&self) -> Solutions {
        self.assignment.get_solutions()
    }

    fn stats(&self) -> SolutionStats {
        SolutionStats {
            conflicts: 0,
            decisions: self.decision_level,
            propagations: self.cnf.num_vars - self.decision_level,
            restarts: 0,
            learnt_clauses: 0,
            removed_clauses: 0,
        }
    }

    fn debug(&mut self) {
        todo!()
    }
}

impl<Config: SolverConfig + Clone> Dpll<Config> {
    fn propagate(&mut self) {
        self.propagator
            .propagate(&mut self.trail, &mut self.assignment, &mut self.cnf);
    }

    fn is_sat(&self) -> bool {
        self.cnf.iter().all(|clause| {
            clause
                .iter()
                .any(|lit| self.assignment.literal_value(*lit) == Some(true))
        })
    }

    fn is_unsat(&self) -> bool {
        self.cnf.iter().any(|clause| {
            clause
                .iter()
                .all(|lit| self.assignment.literal_value(*lit) == Some(false))
        })
    }
}
