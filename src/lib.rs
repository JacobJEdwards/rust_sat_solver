#![deny(missing_docs)]
//! This crate provides various algorithms for SAT (Boolean satisfiability problem) and related puzzles.


/// The `nonogram` module implements the Nonogram puzzle solver, which is a logic puzzle where cells in a grid must be filled based on given clues.
pub mod nonogram;

/// The `sat` module implements the SAT solver, which determines the satisfiability of Boolean 
/// formulas.
pub mod sat;

/// The `sudoku` module implements the Sudoku puzzle solver, which fills a 9x9 grid based on Sudoku rules.
pub mod sudoku;
