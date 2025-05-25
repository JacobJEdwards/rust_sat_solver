#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
pub mod assignment;
pub mod cdcl;

pub mod clause;
pub mod clause_management;
pub mod clause_storage;
pub mod cnf;
pub mod conflict_analysis;
pub mod dimacs;
pub mod dpll;
pub mod expr;
pub mod literal;
pub mod preprocessing;
pub mod propagation;
pub mod restarter;
pub mod solver;
pub mod trail;
pub mod variable_selection;
