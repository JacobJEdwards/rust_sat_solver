use crate::sat::assignment::{Solutions, VecAssignment};
use crate::sat::cdcl::Cdcl;
use crate::sat::clause::Clause;
use crate::sat::cnf::Cnf;
use crate::sat::solver::Solver;
use std::collections::HashMap;
use crate::sat::literal::PackedLiteral;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum TheoryConstraint {
    Leq(String, i32),
    Geq(String, i32),
    Eq(String, i32),
}

#[derive(Debug)]
pub struct SmtSolver {
    cnf: Cnf<PackedLiteral>,
    theory_constraints: Vec<TheoryConstraint>,
    var_mappings: HashMap<(String, i32), i32>,
    // Track actual variable values for theory solving
    var_values: HashMap<String, i32>,
}

impl SmtSolver {
    pub fn new() -> Self {
        Self {
            cnf: Cnf::new(Vec::new()),
            theory_constraints: Vec::new(),
            var_mappings: HashMap::new(),
            var_values: HashMap::new(),
        }
    }

    pub fn add_theory_constraint(&mut self, constraint: TheoryConstraint) {
        match &constraint {
            TheoryConstraint::Leq(var, val) => {
                // When adding x <= val, initialize x to val (tightest bound)
                if let Some(current_val) = self.var_values.get(var) {
                    if *current_val > *val {
                        self.var_values.insert(var.clone(), *val);
                    }
                } else {
                    self.var_values.insert(var.clone(), *val);
                }
            }
            TheoryConstraint::Geq(var, val) => {
                // When adding x >= val, initialize x to val (tightest bound)
                if let Some(current_val) = self.var_values.get(var) {
                    if *current_val < *val {
                        self.var_values.insert(var.clone(), *val);
                    }
                } else {
                    self.var_values.insert(var.clone(), *val);
                }
            }
            TheoryConstraint::Eq(var, val) => {
                // For equality, just set the value
                self.var_values.insert(var.clone(), *val);
            }
        }

        // Create variable mapping if needed
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
        if !self.var_mappings.contains_key(&var_val) {
            let new_lit = self.var_mappings.len() as i32 + 1;
            self.var_mappings.insert(var_val, new_lit);
        }

        self.theory_constraints.push(constraint);
    }
    pub fn solve(&mut self) -> bool {
        let mut iterations = 0;
        let max_iterations = 100; // Add a safety limit to prevent infinite loops

        loop {
            iterations += 1;
            if iterations > max_iterations {
                println!("Reached maximum iterations limit ({max_iterations})");
                return false;
            }

            let mut solver: Cdcl<VecAssignment> = Solver::new(self.cnf.clone());
            let solution = solver.solve();

            if let Some(model) = solution {
                // Update our variable values based on the model
                self.update_var_values(&model);

                if self.check_theory() {
                    println!("Found satisfying assignment: {:?}", self.var_values);
                    return true;
                }
                // Generate a conflict clause based on the violated constraints
                let conflict = self.generate_theory_conflict();
                println!("Theory conflict: {:?}", conflict);

                if conflict.is_empty() {
                    // If we can't generate a meaningful conflict, the problem is unsatisfiable
                    return false;
                }

                self.cnf.add_clause(Clause::from(conflict));
            } else {
                println!("SAT solver found no solution");
                return false;
            }
        }
    }

    // Update variable values based on the SAT model
    fn update_var_values(&mut self, model: &Solutions) {
        // First collect all constraints for each variable
        let mut var_constraints: HashMap<String, Vec<(&TheoryConstraint, bool)>> = HashMap::new();

        for ((var_name, value), lit) in &self.var_mappings {
            let is_true = model.contains(*lit);

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

        // Now process all constraints for each variable
        for (var_name, constraints) in var_constraints {
            let mut lower_bound = i32::MIN;
            let mut upper_bound = i32::MAX;
            let mut eq_values = Vec::new();

            // Process bounds
            for (constraint, is_true) in constraints {
                match constraint {
                    TheoryConstraint::Leq(_, val) => {
                        if is_true {
                            // x <= val is true
                            upper_bound = upper_bound.min(*val);
                        } else {
                            // x <= val is false, so x > val
                            lower_bound = lower_bound.max(*val - 1);
                        }
                    }
                    TheoryConstraint::Geq(_, val) => {
                        if is_true {
                            // x >= val is true
                            lower_bound = lower_bound.max(*val);
                        } else {
                            // x >= val is false, so x < val
                            upper_bound = upper_bound.min(*val + 1);
                        }
                    }
                    TheoryConstraint::Eq(_, val) => {
                        if is_true {
                            // x == val is true
                            eq_values.push(*val);
                        } else {
                            // x == val is false
                            // We need to exclude this value
                        }
                    }
                }
            }

            // Determine final value based on bounds and equality constraints
            let mut final_value = None;

            // First check equalities
            for val in eq_values {
                if val >= lower_bound && val <= upper_bound {
                    final_value = Some(val);
                    break;
                }
            }

            // If no equality matched, pick a value in the range
            if final_value.is_none() {
                if lower_bound <= upper_bound {
                    final_value = Some(lower_bound); // Choose smallest valid value
                } else {
                    // This is a conflict - we'll let the conflict generation handle it
                    // For now, just pick a value
                    final_value = Some(lower_bound);
                }
            }

            // Update the variable
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

    // Check if the current variable values satisfy all theory constraints
    pub fn check_theory(&self) -> bool {
        for constraint in &self.theory_constraints {
            match constraint {
                TheoryConstraint::Leq(var, val) => {
                    if let Some(&var_val) = self.var_values.get(var) {
                        if var_val > *val {
                            println!(
                                "Constraint violated: {} <= {} (actual: {})",
                                var, val, var_val
                            );
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

    // Generate a conflict clause based on violated constraints
    pub fn generate_theory_conflict(&self) -> Vec<i32> {
        let mut conflict_lits = Vec::new();
        let mut violated_constraints = Vec::new();

        // First, collect all violated constraints
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

        // Generate conflict based on violated constraints
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

        // If no specific conflicts, create a general conflict
        if conflict_lits.is_empty() && !self.var_mappings.is_empty() {
            // Choose a subset of assignments to exclude
            for ((var, _), lit) in self.var_mappings.iter().take(3) {
                // Limit to prevent huge clauses
                if self.var_values.contains_key(var) {
                    conflict_lits.push(-lit);
                }
            }
        }

        conflict_lits
    }
}
