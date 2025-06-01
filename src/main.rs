//! # sat_solver
//!
//! `sat_solver` is a configurable command-line SAT (Satisfiability) solver.
//! It can parse and solve problems in CNF (Conjunctive Normal Form) DIMACS format,
//! CNF provided as plain text, and also includes specialised solvers for Sudoku
//! and Nonogram puzzles by converting them to CNF.
//!
//! The solver supports two main algorithms:
//! 1.  **DPLL (Davis-Putnam-Logemann-Loveland)**: A classic backtracking-based algorithm.
//! 2.  **CDCL (Conflict-Driven Clause Learning)**: A more advanced algorithm that learns from conflicts
//!     to prune the search space more effectively.
//!
//! ## Features
//!
//! -   **Multiple Input Formats**:
//!     -   DIMACS CNF files (`.cnf`)
//!     -   Plain text CNF
//!     -   Sudoku puzzle files
//!     -   Nonogram puzzle files
//! -   **Configurable Solver**: Choose between DPLL and CDCL.
//! -   **Debugging**: Option to print detailed debug information during solving.
//! -   **Verification**: Option to verify the found solution against the CNF formula.
//! -   **Statistics**: Provides detailed statistics about the solving process, including
//!     parse time, solve time, number of conflicts, decisions, propagations, restarts,
//!     and memory usage.
//! -   **Solution Printing**: Option to print the satisfying assignment.
//! -   **DIMACS Export**: For Sudoku puzzles, it can export the generated CNF to a DIMACS file.
//! -   **Memory Management**: Uses `tikv-jemallocator` for memory allocation and provides
//!     memory usage statistics.
//!
//! ## Usage
//!
//! The application is driven by command-line arguments.
//!
//! ### General Syntax
//!
//! ```sh
//! sat_solver [GLOBAL_OPTIONS] [SUBCOMMAND]
//! ```
//!
//! ### Global Argument
//!
//! -   `path`: If provided as the *only* argument (without a subcommand), it's treated as
//!     a path to a DIMACS .cnf file to be solved.
//!
//!     ```sh
//!     sat_solver <path_to_cnf_file>
//!     ```
//!
//! ### Subcommands
//!
//! 1.  **`file`**: Solve a CNF file in DIMACS format.
//!     ```sh
//!     sat_solver file --path <path_to_cnf_file> [OPTIONS]
//!     ```
//!
//! 2.  **`text`**: Solve a CNF formula provided as plain text.
//!     ```sh
//!     sat_solver text --input "<cnf_string>" [OPTIONS]
//!     # Example: sat_solver text --input "1 -2 0\n2 3 0"
//!     ```
//!
//! 3.  **`sudoku`**: Solve a Sudoku puzzle.
//!     ```sh
//!     sat_solver sudoku --path <path_to_sudoku_file> [OPTIONS]
//!     # Optionally export to DIMACS:
//!     sat_solver sudoku --path <path_to_sudoku_file> --export-dimacs [OPTIONS]
//!     ```
//!
//!
//! ### Common Options (available for all subcommands and global file path)
//!
//! These options can be passed to the main command or to specific subcommands.
//!
//! -   `-d, --debug`: Enable debug output (default: `false`).
//! -   `--verify`: Enable verification of the solution (default: `true`).
//! -   `--stats`: Enable printing of statistics (default: `true`).
//! -   `-p, --print-solution`: Enable printing of the solution model (default: `false`).
//! -   `-s, --solver <SOLVER_NAME>`: Solver type. Can be `cdcl` or `dpll` (default: `cdcl`).
//!
//! ## Example Uses
//!
//! ```sh
//! # Solve a DIMACS file using the default CDCL solver
//! sat_solver problem.cnf
//!
//! # Solve a DIMACS file using DPLL and print debug info
//! sat_solver file --path problem.cnf --solver dpll --debug
//!
//! # Solve a Sudoku puzzle and export its CNF representation
//! sat_solver sudoku --path puzzle.sudoku --export-dimacs
//!
//! # Solve a Nonogram puzzle and print the solution
//! sat_solver nonogram --path puzzle.nonogram --print-solution
//!
//! # Solve a CNF formula from text input
//! sat_solver text --input "1 2 0\n-1 0"
//! ```
//!
//! This file (`main.rs`) contains the main entry point, CLI parsing logic,
//! and orchestrates the solving process based on user input.
//! It uses modules `sat`, `sudoku`, and `nonogram` for specialised logic.

use crate::command_line::cli::{Cli, Commands, solve_and_report, solve_dir, solve_nonogram, solve_sudoku, CommonOptions};
use crate::sat::dimacs::{parse_dimacs_text, parse_file};
use clap::{CommandFactory, Parser};

pub mod command_line;
pub mod nonogram;
pub mod sat;
pub mod sudoku;

/// Global allocator using `tikv-jemallocator` for potentially better performance
/// and memory usage tracking.
#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

/// Main entry point of the sat solver application.
///
/// Parses command-line arguments, dispatches to the appropriate command handler,
/// and manages the overall execution flow.
fn main() {
    let cli = Cli::parse();

    if let Some(Commands::Completions { shell }) = &cli.command {
        let mut cmd = <Cli as CommandFactory>::command();
        let cmd_name = cmd.get_name().to_string();
        clap_complete::generate(*shell, &mut cmd, cmd_name, &mut std::io::stdout());
        return;
    }

    // handle the case where a path is provided globally without a subcommand
    // this defaults to solving a DIMACS file
    if let Some(path) = &cli.path {
        if cli.command.is_none() {
            if !path.exists() {
                eprintln!("File does not exist: {}", path.display());
                std::process::exit(1);
            }

            if path.is_dir() {
                if let Err(e) = solve_dir(path, &cli.common) {
                    eprintln!("Error solving directory: {}", e);
                    std::process::exit(1);
                }
                return;
            }
            
            if path.extension().is_some_and(|ext| ext == "sudoku") {
                if let Err(e) = solve_sudoku(path, false, &CommonOptions::default()) {
                    eprintln!("Error solving Sudoku: {}", e);
                    std::process::exit(1);
                }
                return;
            }

            // if nonogram, we handle it separately
            if path.extension().is_some_and(|ext| ext == "nonogram") {
                if let Err(e) = solve_nonogram(path, &CommonOptions::default()) {
                    eprintln!("Error solving Nonogram: {}", e);
                    std::process::exit(1);
                }
                return;
            }

            let time = std::time::Instant::now();
            let cnf = parse_file(path)
                .unwrap_or_else(|_| panic!("Failed to parse file: {}", path.display()));
            let elapsed = time.elapsed();

            solve_and_report(&cnf, &cli.common, Some(path), elapsed);
            return;
        }
    }

    match cli.command {
        Some(Commands::File { path, common }) => {
            if !path.exists() {
                eprintln!("File does not exist: {}", path.display());
                std::process::exit(1);
            }

            if path.is_dir() {
                let result = solve_dir(&path, &common);
                if let Err(e) = result {
                    eprintln!("Error solving directory: {}", e);
                    std::process::exit(1);
                }
                return;
            }

            // if sudoku, we handle it separately
            if path.extension().is_some_and(|ext| ext == "sudoku") {
                if let Err(e) = solve_sudoku(&path, false, &common) {
                    eprintln!("Error solving Sudoku: {}", e);
                    std::process::exit(1);
                }
                return;
            }

            // if nonogram, we handle it separately
            if path.extension().is_some_and(|ext| ext == "nonogram") {
                if let Err(e) = solve_nonogram(&path, &common) {
                    eprintln!("Error solving Nonogram: {}", e);
                    std::process::exit(1);
                }
                return;
            }

            let time = std::time::Instant::now();
            let cnf = parse_file(&path)
                .unwrap_or_else(|_| panic!("Failed to parse file: {}", path.display()));
            let elapsed = time.elapsed();

            solve_and_report(&cnf, &common, Some(&path), elapsed);
        }

        Some(Commands::Text { input, common }) => {
            let time = std::time::Instant::now();
            let result = parse_dimacs_text(&input);
            let cnf = result.unwrap_or_else(|_| panic!("Failed to parse input text: {}", input));
            let elapsed = time.elapsed();

            solve_and_report(&cnf, &common, None, elapsed);
        }
        Some(Commands::Sudoku {
            path,
            common,
            export_dimacs,
        }) => {
            if let Err(e) = solve_sudoku(&path, export_dimacs, &common) {
                eprintln!("Error solving Sudoku: {}", e);
                std::process::exit(1);
            }
        }
        Some(Commands::Nonogram { path, common }) => {
            if let Err(e) = solve_nonogram(&path, &common) {
                eprintln!("Error solving Nonogram: {}", e);
                std::process::exit(1);
            }
        }
        None => {
            if cli.path.is_none() {
                eprintln!("No command provided. Use --help for more information.");
                std::process::exit(1);
            }
        }
        Some(Commands::Completions { .. }) => unreachable!(),
    }
}

#[cfg(test)]
mod tests {}
