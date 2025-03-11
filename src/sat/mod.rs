#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
pub mod assignment;
pub mod clause;
pub mod cnf;
pub mod conflict_analysis;
pub mod expr;
pub mod literal;
pub mod propagation;
pub mod state;
pub mod trail;
pub mod variable_selection;
pub mod watch;
pub mod dimacs;
pub mod solver;
pub mod phase_saving;
pub mod restarter;
