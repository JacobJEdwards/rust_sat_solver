#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]

/// Represents the assignment of variables in a SAT solver.
pub mod assignment;

/// The `cdcl` module implements the Conflict-Driven Clause Learning (CDCL) algorithm for SAT solving.
pub mod cdcl;

/// The `cnf` module provides functionality for working with Conjunctive Normal Form (CNF) representations.
pub mod clause;

/// The `clause_management` module handles the management of clauses in a SAT solver.
pub mod clause_management;

/// The `clause_storage` module provides storage and retrieval mechanisms for clauses in a SAT solver.
pub mod clause_storage;

/// The `cnf` module provides functionality for parsing and manipulating CNF (Conjunctive Normal Form) formulas.
pub mod cnf;

/// The `conflict_analysis` module implements conflict analysis techniques used in SAT solvers.
pub mod conflict_analysis;

/// The `dimacs` module handles parsing DIMACS format files, which are commonly used for representing SAT problems.
pub mod dimacs;

/// The `dpll` module implements the DPLL (Davis-Putnam-Logemann-Loveland) algorithm for SAT solving.
pub mod dpll;

/// The `expr` module provides functionality for working with Boolean expressions, including parsing and manipulation.
pub mod expr;

/// The `heuristic` module implements various heuristics for variable selection and decision-making in SAT solvers.
pub mod literal;

/// The `literal` module provides functionality for working with literals in SAT problems.
pub mod preprocessing;

/// The `propagation` module implements unit propagation and other propagation techniques used in SAT solvers.
pub mod propagation;

/// The `restarter` module implements restarts in SAT solvers, which can help escape from difficult regions of the search space.
pub mod restarter;

/// The `solver` module provides the main interface for solving SAT problems using various algorithms and techniques.
pub mod solver;

/// The `trail` module implements a trail data structure used in SAT solvers to keep track of variable assignments and decisions.
pub mod trail;

/// The `variable_selection` module implements various strategies for selecting variables during the solving process.
pub mod variable_selection;
