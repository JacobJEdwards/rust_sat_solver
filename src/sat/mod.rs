#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
pub mod assignment;
pub mod cdcl;
pub mod clause;
pub mod cnf;
pub mod conflict_analysis;
pub mod dimacs;
pub mod expr;
pub mod literal;
pub mod phase_saving;
pub mod preprocessing;
pub mod restarter;
pub mod solver;
pub mod trail;
pub mod variable_selection;
pub mod watch;
