use crate::sat::assignment::VecAssignment;
use crate::sat::cdcl::Cdcl;
use crate::sat::clause::Clause;
use crate::sat::clause_storage::LiteralStorage;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use crate::sat::propagation::WatchedLiterals;
use crate::sat::restarter::Luby;
use crate::sat::solver::SolverConfig;
use crate::sat::solver::{Solutions, Solver};
use crate::sat::variable_selection::Vsids;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::num::NonZeroI32;
use crate::sat::clause_management::LbdClauseManagement;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum TheoryConstraint {
    Leq(String, i32),
    Geq(String, i32),
    Eq(String, i32),
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SmtSolver<L: Literal, S: LiteralStorage<L>> {
    cnf: Cnf<L, S>,
    theory_constraints: Vec<TheoryConstraint>,
    var_mappings: HashMap<(String, i32), i32>,
    var_values: HashMap<String, i32>,
}

#[derive(Debug, Clone)]
struct LiteralConfig<L: Literal>(PhantomData<*const L>);

impl<L: Literal> SolverConfig for LiteralConfig<L> {
    type Assignment = VecAssignment;
    type VariableSelector = Vsids;
    type Literal = L;
    type LiteralStorage = Vec<L>;
    type Restarter = Luby<50>;
    type Propagator = WatchedLiterals<L, Self::LiteralStorage, Self::Assignment>;
    type ClauseManager = LbdClauseManagement<Self::Literal, Self::LiteralStorage, 10>;
}

impl<L: Literal> SmtSolver<L, Vec<L>> {
    #[must_use]
    pub fn new() -> Self {
        Self {
            cnf: Cnf::<L, Vec<L>>::new(Vec::new()),
            theory_constraints: Vec::new(),
            var_mappings: HashMap::new(),
            var_values: HashMap::new(),
        }
    }

    pub fn add_theory_constraint(&mut self, constraint: TheoryConstraint) {
        match &constraint {
            TheoryConstraint::Leq(var, val) => {
                if let Some(current_val) = self.var_values.get(var) {
                    if *current_val > *val {
                        self.var_values.insert(var.clone(), *val);
                    }
                } else {
                    self.var_values.insert(var.clone(), *val);
                }
            }
            TheoryConstraint::Geq(var, val) => {
                if let Some(current_val) = self.var_values.get(var) {
                    if *current_val < *val {
                        self.var_values.insert(var.clone(), *val);
                    }
                } else {
                    self.var_values.insert(var.clone(), *val);
                }
            }
            TheoryConstraint::Eq(var, val) => {
                self.var_values.insert(var.clone(), *val);
            }
        }

        let var_name = match &constraint {
            TheoryConstraint::Geq(var, _)
            | TheoryConstraint::Eq(var, _)
            | TheoryConstraint::Leq(var, _) => var,
        };

        let var_value = match &constraint {
            TheoryConstraint::Geq(_, c)
            | TheoryConstraint::Eq(_, c)
            | TheoryConstraint::Leq(_, c) => c,
        };

        let var_val = (var_name.clone(), *var_value);
        #[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
        if !self.var_mappings.contains_key(&var_val) {
            let new_lit = self.var_mappings.len().wrapping_add(1) as i32;
            self.var_mappings.insert(var_val, new_lit);
        }

        self.theory_constraints.push(constraint);
    }
    pub fn solve(&mut self) -> bool {
        let mut iterations = 0;
        let max_iterations = 100;

        loop {
            iterations += 1;
            if iterations > max_iterations {
                println!("Reached maximum iterations limit ({max_iterations})");
                return false;
            }

            let mut solver: Cdcl<LiteralConfig<L>> = Solver::new(self.cnf.clone());
            let solution = solver.solve();

            if let Some(model) = solution {
                self.update_var_values(&model);

                if self.check_theory() {
                    println!("Found satisfying assignment: {:?}", self.var_values);
                    return true;
                }
                let conflict = self.generate_theory_conflict();
                println!("Theory conflict: {conflict:?}");

                if conflict.is_empty() {
                    return false;
                }

                self.cnf.add_clause(Clause::from(conflict));
            } else {
                println!("SAT solver found no solution");
                return false;
            }
        }
    }

    fn update_var_values(&mut self, model: &Solutions) {
        let mut var_constraints: HashMap<String, Vec<(&TheoryConstraint, bool)>> = HashMap::new();

        for ((var_name, value), lit) in &self.var_mappings {
            let is_true = model.check(NonZeroI32::new(*lit).unwrap());

            for constraint in &self.theory_constraints {
                match constraint {
                    TheoryConstraint::Leq(var, val) if var == var_name && *val == *value => {
                        var_constraints
                            .entry(var_name.clone())
                            .or_default()
                            .push((constraint, is_true));
                    }
                    TheoryConstraint::Geq(var, val) if var == var_name && *val == *value => {
                        var_constraints
                            .entry(var_name.clone())
                            .or_default()
                            .push((constraint, is_true));
                    }
                    TheoryConstraint::Eq(var, val) if var == var_name && *val == *value => {
                        var_constraints
                            .entry(var_name.clone())
                            .or_default()
                            .push((constraint, is_true));
                    }
                    _ => {}
                }
            }
        }

        for (var_name, constraints) in var_constraints {
            let mut lower_bound = i32::MIN;
            let mut upper_bound = i32::MAX;
            let mut eq_values = Vec::new();

            for (constraint, is_true) in constraints {
                match constraint {
                    TheoryConstraint::Leq(_, val) => {
                        if is_true {
                            upper_bound = upper_bound.min(*val);
                        } else {
                            lower_bound = lower_bound.max(*val - 1);
                        }
                    }
                    TheoryConstraint::Geq(_, val) => {
                        if is_true {
                            lower_bound = lower_bound.max(*val);
                        } else {
                            upper_bound = upper_bound.min(*val + 1);
                        }
                    }
                    TheoryConstraint::Eq(_, val) => {
                        if is_true {
                            eq_values.push(*val);
                        } else {
                        }
                    }
                }
            }

            let mut final_value = None;

            for val in eq_values {
                if val >= lower_bound && val <= upper_bound {
                    final_value = Some(val);
                    break;
                }
            }

            if final_value.is_none() {
                if lower_bound <= upper_bound {
                    final_value = Some(lower_bound);
                } else {
                    final_value = Some(lower_bound);
                }
            }

            if let Some(val) = final_value {
                self.var_values.insert(var_name, val);
            }
        }

        println!("Updated variable values: {:?}", self.var_values);
    }
    fn find_constraint_type(&self, var_name: &String, value: i32) -> Option<TheoryConstraint> {
        for constraint in &self.theory_constraints {
            match constraint {
                TheoryConstraint::Leq(name, val) if name == var_name && *val == value => {
                    return Some(constraint.clone());
                }
                TheoryConstraint::Geq(name, val) if name == var_name && *val == value => {
                    return Some(constraint.clone());
                }
                TheoryConstraint::Eq(name, val) if name == var_name && *val == value => {
                    return Some(constraint.clone());
                }
                _ => continue,
            }
        }
        None
    }

    pub fn check_theory(&self) -> bool {
        for constraint in &self.theory_constraints {
            match constraint {
                TheoryConstraint::Leq(var, val) => {
                    if let Some(&var_val) = self.var_values.get(var) {
                        if var_val > *val {
                            println!("Constraint violated: {var} <= {val} (actual: {var_val})",);
                            return false;
                        }
                    }
                }
                TheoryConstraint::Geq(var, val) => {
                    if let Some(&var_val) = self.var_values.get(var) {
                        if var_val < *val {
                            println!(
                                "Constraint violated: {} >= {} (actual: {})",
                                var, val, var_val
                            );
                            return false;
                        }
                    }
                }
                TheoryConstraint::Eq(var, val) => {
                    if let Some(&var_val) = self.var_values.get(var) {
                        if var_val != *val {
                            println!(
                                "Constraint violated: {} == {} (actual: {})",
                                var, val, var_val
                            );
                            return false;
                        }
                    }
                }
            }
        }

        true
    }

    pub fn generate_theory_conflict(&self) -> Vec<i32> {
        let mut conflict_lits = Vec::new();
        let mut violated_constraints = Vec::new();

        for constraint in &self.theory_constraints {
            match constraint {
                TheoryConstraint::Leq(var, val) => {
                    if let Some(&var_val) = self.var_values.get(var) {
                        if var_val > *val {
                            violated_constraints.push(constraint.clone());
                        }
                    }
                }
                TheoryConstraint::Geq(var, val) => {
                    if let Some(&var_val) = self.var_values.get(var) {
                        if var_val < *val {
                            violated_constraints.push(constraint.clone());
                        }
                    }
                }
                TheoryConstraint::Eq(var, val) => {
                    if let Some(&var_val) = self.var_values.get(var) {
                        if var_val != *val {
                            violated_constraints.push(constraint.clone());
                        }
                    }
                }
            }
        }

        for constraint in violated_constraints {
            match constraint {
                TheoryConstraint::Leq(var, val) => {
                    if let Some(&lit) = self.var_mappings.get(&(var, val)) {
                        conflict_lits.push(-lit);
                    }
                }
                TheoryConstraint::Geq(var, val) => {
                    if let Some(&lit) = self.var_mappings.get(&(var, val)) {
                        conflict_lits.push(-lit);
                    }
                }
                TheoryConstraint::Eq(var, val) => {
                    if let Some(&lit) = self.var_mappings.get(&(var, val)) {
                        conflict_lits.push(-lit);
                    }
                }
            }
        }

        if conflict_lits.is_empty() && !self.var_mappings.is_empty() {
            for ((var, _), lit) in self.var_mappings.iter().take(3) {
                if self.var_values.contains_key(var) {
                    conflict_lits.push(-lit);
                }
            }
        }

        conflict_lits
    }
}
