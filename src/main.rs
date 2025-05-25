//! # SATSolver
//!
//! `SATSolver` is a configurable command-line SAT (Satisfiability) solver.
//! It can parse and solve problems in CNF (Conjunctive Normal Form) DIMACS format,
//! CNF provided as plain text, and also includes specialized solvers for Sudoku
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
//! satsolver [GLOBAL_OPTIONS] [SUBCOMMAND]
//! ```
//!
//! ### Global Argument
//!
//! -   `path`: If provided as the *only* argument (without a subcommand), it's treated as
//!     a path to a DIMACS .cnf file to be solved.
//!
//!     ```sh
//!     satsolver <path_to_cnf_file>
//!     ```
//!
//! ### Subcommands
//!
//! 1.  **`file`**: Solve a CNF file in DIMACS format.
//!     ```sh
//!     satsolver file --path <path_to_cnf_file> [OPTIONS]
//!     ```
//!
//! 2.  **`text`**: Solve a CNF formula provided as plain text.
//!     ```sh
//!     satsolver text --input "<cnf_string>" [OPTIONS]
//!     # Example: satsolver text --input "1 -2 0\n2 3 0"
//!     ```
//!
//! 3.  **`sudoku`**: Solve a Sudoku puzzle.
//!     ```sh
//!     satsolver sudoku --path <path_to_sudoku_file> [OPTIONS]
//!     # Optionally export to DIMACS:
//!     satsolver sudoku --path <path_to_sudoku_file> --export-dimacs [OPTIONS]
//!     ```
//!
//! 4.  **`nonogram`**: Solve a Nonogram puzzle.
//!     ```sh
//!     satsolver nonogram --path <path_to_nonogram_file> [OPTIONS]
//!     ```
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
//! ## Example Invocations
//!
//! ```sh
//! # Solve a DIMACS file using the default CDCL solver
//! satsolver problem.cnf
//!
//! # Solve a DIMACS file using DPLL and print debug info
//! satsolver file --path problem.cnf --solver dpll --debug
//!
//! # Solve a Sudoku puzzle and export its CNF representation
//! satsolver sudoku --path puzzle.sudoku --export-dimacs
//!
//! # Solve a Nonogram puzzle and print the solution
//! satsolver nonogram --path puzzle.nonogram --print-solution
//!
//! # Solve a CNF formula from text input
//! satsolver text --input "1 2 0\n-1 0"
//! ```
//!
//! This file (`main.rs`) contains the main entry point, CLI parsing logic,
//! and orchestrates the solving process based on user input.
//! It uses modules `sat`, `sudoku`, and `nonogram` for specialized logic.

use crate::sat::cdcl::Cdcl;
use crate::sat::cnf::Cnf;
use crate::sat::dimacs::parse_file;
use crate::sat::dpll::Dpll;
use crate::sat::solver::{DefaultConfig, SolutionStats, Solutions, Solver};
use clap::{Args, Parser, Subcommand};
use itertools::Itertools;
use std::time::Duration;
use tikv_jemalloc_ctl::{epoch, stats};

// Modules for specific problem domains and SAT solver internals.
// These are expected to be defined in other files (e.g., sat.rs, nonogram.rs, sudoku.rs).
mod nonogram;
mod sat;
mod sudoku;

/// Global allocator using `tikv-jemallocator` for potentially better performance
/// and memory usage tracking.
#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

/// Defines the command-line interface for the SATSolver application.
///
/// Uses `clap` for parsing arguments.
#[derive(Parser, Debug)]
#[command(name = "SATSolver", version, about = "A configurable SAT solver")]
struct Cli {
    /// An optional global path argument. If provided without a subcommand,
    /// it's treated as the path to a DIMACS .cnf file to solve.
    #[arg(global = true)]
    path: Option<String>,

    /// Specifies the subcommand to execute (e.g., `file`, `text`, `sudoku`, `nonogram`).
    #[clap(subcommand)]
    command: Option<Commands>,

    /// Common options applicable to all commands.
    #[command(flatten)]
    common: CommonOptions,
}

/// Enumerates the available subcommands for the SATSolver.
#[derive(Subcommand, Debug)]
enum Commands {
    /// Solve a CNF file in DIMACS format.
    File {
        /// Path to the DIMACS .cnf file.
        #[arg(short, long)]
        path: String,

        /// Common options for this subcommand.
        #[command(flatten)]
        common: CommonOptions,
    },

    /// Solve a CNF formula provided as plain text.
    Text {
        /// Literal CNF input as a string (e.g., "1 -2 0\n2 3 0").
        /// Each line represents a clause, literals are space-separated, and 0 terminates a clause.
        #[arg(short, long)]
        input: String,

        /// Common options for this subcommand.
        #[command(flatten)]
        common: CommonOptions,
    },

    /// Solve a Sudoku puzzle.
    /// The Sudoku puzzle is converted into a CNF formula, which is then solved.
    Sudoku {
        /// Path to the Sudoku file. The format of this file is defined by the `sudoku::solver::parse_sudoku_file` function.
        #[arg(short, long)]
        path: String,

        /// If true, the generated DIMACS CNF representation of the Sudoku puzzle will be printed and saved to a file.
        #[arg(short, long, default_value_t = false)]
        export_dimacs: bool,

        /// Common options for this subcommand.
        #[command(flatten)]
        common: CommonOptions,
    },

    /// Solve a Nonogram puzzle.
    /// The Nonogram puzzle is converted into a CNF formula, which is then solved.
    Nonogram {
        /// Path to the Nonogram file. The format of this file is defined by the `nonogram::solver::parse_nonogram_file` function.
        #[arg(short, long)]
        path: String,

        /// Common options for this subcommand.
        #[command(flatten)]
        common: CommonOptions,
    },
}

/// Defines common command-line options shared across different subcommands.
#[derive(Args, Debug, Default)]
struct CommonOptions {
    /// Enable debug output, providing more verbose logging during the solving process.
    #[arg(short, long, default_value_t = false)]
    debug: bool,

    /// Enable verification of the found solution. If a solution is found, it's checked against the original CNF.
    #[arg(short, long, default_value_t = true)]
    verify: bool,

    /// Enable printing of performance and problem statistics after solving.
    #[arg(short, long, default_value_t = true)]
    stats: bool,

    /// Enable printing of the satisfying assignment (model) if the formula is satisfiable.
    #[arg(short, long, default_value_t = false)]
    print_solution: bool,

    /// Specifies the SAT solver algorithm to use.
    /// Supported values are "cdcl" (Conflict-Driven Clause Learning) and "dpll" (Davis-Putnam-Logemann-Loveland).
    #[arg(short, long, default_value_t = String::from("cdcl"))]
    solver: String,
}

/// Main entry point of the SATSolver application.
///
/// Parses command-line arguments, dispatches to the appropriate command handler,
/// and manages the overall execution flow.
fn main() {
    let cli = Cli::parse();

    // Handle the case where a path is provided globally without a subcommand.
    // This defaults to solving a DIMACS file.
    if let Some(path) = cli.path.clone() {
        if cli.command.is_none() {
            let time = std::time::Instant::now();
            let cnf =
                parse_file(&path).unwrap_or_else(|_| panic!("Failed to parse file: {}", path));
            let elapsed = time.elapsed();

            solve_and_report(cnf, cli.common, Some(&path), elapsed);
            return;
        }
    }

    // Match on the specified subcommand.
    match cli.command {
        Some(Commands::File { path, common }) => {
            let time = std::time::Instant::now();
            let cnf =
                parse_file(&path).unwrap_or_else(|_| panic!("Failed to parse file: {}", path));
            let elapsed = time.elapsed();

            solve_and_report(cnf, common, Some(&path), elapsed);
        }

        Some(Commands::Text { input, common }) => {
            let time = std::time::Instant::now();
            let clauses = parse_textual_cnf(&input);
            let cnf = Cnf::from(clauses);
            let elapsed = time.elapsed();

            solve_and_report(cnf, common, None, elapsed);
        }
        Some(Commands::Sudoku {
            path,
            common,
            export_dimacs,
        }) => {
            let time = std::time::Instant::now();
            // Assumes `sudoku::solver::parse_sudoku_file` exists and parses a Sudoku puzzle.
            let sudoku = sudoku::solver::parse_sudoku_file(&path);

            match sudoku {
                Ok(sudoku) => {
                    println!("Parsed Sudoku:\n{sudoku}");

                    // Assumes `sudoku.to_cnf()` converts the puzzle to a CNF formula.
                    let cnf = sudoku.to_cnf();

                    if export_dimacs {
                        let dimacs = cnf.to_string();
                        println!("DIMACS:\n{dimacs}");

                        let path_name = path.to_string();
                        let dimacs_path = format!("{}.cnf", path_name);
                        std::fs::write(&dimacs_path, dimacs).unwrap_or_else(|e| {
                            panic!("Unable to write file {}: {}", dimacs_path, e)
                        });
                        println!("DIMACS written to: {dimacs_path}");
                    }

                    let parse_time = time.elapsed();
                    let (sol, elapsed, solver_stats) =
                        solve(cnf.clone(), common.debug, Some(&path), &common.solver);

                    // Advance epoch for memory stats collection if using jemalloc.
                    // This helps in getting more accurate memory stats related to the solving phase.
                    epoch::advance().unwrap();
                    let allocated_bytes = stats::allocated::mib().unwrap().read().unwrap();
                    let resident_bytes = stats::resident::mib().unwrap().read().unwrap();
                    let allocated_mib = allocated_bytes as f64 / (1024.0 * 1024.0);
                    let resident_mib = resident_bytes as f64 / (1024.0 * 1024.0);

                    if common.verify {
                        verify_solution(cnf.clone(), &sol);
                    }

                    if common.stats {
                        print_stats(
                            parse_time,
                            elapsed,
                            &cnf,
                            &solver_stats,
                            allocated_mib,
                            resident_mib,
                            common.print_solution,
                            &sol,
                        );
                    }

                    if let Some(sol_values) = sol {
                        // Assumes `sudoku.decode(&sol_values)` decodes the SAT solution back to a Sudoku grid.
                        let solution_grid = sudoku.decode(&sol_values);
                        println!("Solution: {solution_grid}");
                    } else {
                        println!("No solution found");
                    }
                }
                Err(e) => {
                    eprintln!("Error parsing Sudoku file: {}", e);
                }
            }
        }
        Some(Commands::Nonogram { path, common }) => {
            let time = std::time::Instant::now();
            // Assumes `nonogram::solver::parse_nonogram_file` exists.
            let nonogram = nonogram::solver::parse_nonogram_file(&path);
            match nonogram {
                Ok(nonogram) => {
                    println!("Parsed Nonogram:\n{nonogram}");

                    // Assumes `nonogram.to_cnf()` converts the puzzle to a CNF formula.
                    let cnf = nonogram.to_cnf();

                    let parse_time = time.elapsed();
                    let (sol, elapsed, solver_stats) =
                        solve(cnf.clone(), common.debug, Some(&path), &common.solver);

                    epoch::advance().unwrap();
                    let allocated_bytes = stats::allocated::mib().unwrap().read().unwrap();
                    let resident_bytes = stats::resident::mib().unwrap().read().unwrap();
                    let allocated_mib = allocated_bytes as f64 / (1024.0 * 1024.0);
                    let resident_mib = resident_bytes as f64 / (1024.0 * 1024.0);

                    if common.verify {
                        verify_solution(cnf.clone(), &sol);
                    }

                    if common.stats {
                        print_stats(
                            parse_time,
                            elapsed,
                            &cnf,
                            &solver_stats,
                            allocated_mib,
                            resident_mib,
                            common.print_solution,
                            &sol,
                        );
                    }

                    if let Some(sol_values) = sol {
                        // Assumes `nonogram.decode(&sol_values)` decodes the SAT solution.
                        let solution_grid = nonogram.decode(&sol_values);
                        for row in solution_grid.iter() {
                            println!("{:?}", row); // Example: prints each row of the decoded Nonogram.
                        }
                    } else {
                        println!("No solution found");
                    }
                }
                Err(e) => {
                    eprintln!("Error parsing Nonogram file: {}", e);
                }
            }
        }
        None => {
            // This case is reached if no subcommand was provided and `cli.path` was also None.
            if cli.path.is_none() {
                eprintln!("No command provided. Use --help for more information.");
                std::process::exit(1);
            }
            // If `cli.path` was Some, it would have been handled by the first `if` block.
        }
    }
}

/// Verifies a given solution (`sol`) against a CNF formula (`cnf`).
///
/// Prints whether the verification was successful. If verification fails, it panics.
/// If `sol` is `None` (indicating UNSAT), it prints "UNSAT".
///
/// # Arguments
/// * `cnf` - The CNF formula to verify against.
/// * `sol` - An `Option<Solutions>` representing the model found by the solver.
fn verify_solution(cnf: Cnf, sol: &Option<Solutions>) {
    if let Some(sol_values) = sol.clone() {
        let ok = cnf.verify(&sol_values);
        println!("Verified: {:?}", ok);
        if !ok {
            panic!("Solution failed verification!");
        }
    } else {
        println!("UNSAT");
    }
}

/// Solves a CNF formula using the specified solver.
///
/// # Arguments
/// * `cnf` - The CNF formula to solve.
/// * `debug` - Boolean flag to enable debug printing.
/// * `label` - An optional label for the problem (e.g., file path), used in debug output.
/// * `solver_name` - The name of the solver to use ("dpll" or "cdcl").
///
/// # Returns
/// A tuple containing:
/// * `Option<Solutions>`: The solution (model) if found, otherwise `None`.
/// * `Duration`: The time taken to solve the formula.
/// * `SolutionStats`: Statistics collected during the solving process.
///
/// # Panics
/// Panics if `solver_name` is not "dpll" or "cdcl".
fn solve(
    cnf: Cnf,
    debug: bool,
    label: Option<&str>,
    solver_name: &str,
) -> (Option<Solutions>, Duration, SolutionStats) {
    if let Some(name) = label {
        println!("Solving: {:?}", name);
    }

    if debug {
        println!("CNF: {}", cnf);
        println!("Variables: {}", cnf.num_vars);
        println!("Clauses: {}", cnf.clauses.len());
        println!("Literals: {}", cnf.lits.len());
    }

    match solver_name.to_lowercase().as_str() {
        "dpll" => solve_dpll(cnf, debug),
        "cdcl" => solve_cdcl(cnf, debug),
        _ => panic!("Unknown solver name {}", solver_name),
    }
}

/// Solves a CNF formula using the CDCL solver.
///
/// # Arguments
/// * `cnf` - The CNF formula to solve.
/// * `debug` - Boolean flag to enable debug printing.
///
/// # Returns
/// See `solve` function return type.
fn solve_cdcl(cnf: Cnf, debug: bool) -> (Option<Solutions>, Duration, SolutionStats) {
    // Advance epoch for jemalloc stats, helps isolate memory usage for this solving phase.
    epoch::advance().unwrap();

    let time = std::time::Instant::now();

    let mut solver = Cdcl::<DefaultConfig>::new(cnf);
    let sol = solver.solve();

    let elapsed = time.elapsed();

    if debug {
        println!("Solution: {:?}", sol);
        println!("Time: {:?}", elapsed);
    }

    (sol, elapsed, solver.stats())
}

/// Solves a CNF formula using the DPLL solver.
///
/// # Arguments
/// * `cnf` - The CNF formula to solve.
/// * `debug` - Boolean flag to enable debug printing.
///
/// # Returns
/// See `solve` function return type.
fn solve_dpll(cnf: Cnf, debug: bool) -> (Option<Solutions>, Duration, SolutionStats) {
    epoch::advance().unwrap();

    let time = std::time::Instant::now();

    let mut solver = Dpll::<DefaultConfig>::new(cnf);
    let sol = solver.solve();

    let elapsed = time.elapsed();

    if debug {
        println!("Solution: {:?}", sol);
        println!("Time: {:?}", elapsed);
    }

    (sol, elapsed, solver.stats())
}

/// Parses a CNF file, solves it, and reports results including stats and verification.
///
/// This function is a convenience wrapper around `solve`, `verify_solution`, and `print_stats`.
///
/// # Arguments
/// * `cnf` - The CNF formula, typically parsed from a file or text.
/// * `common` - `CommonOptions` providing solver configuration (debug, verify, stats, solver type).
/// * `label` - An optional label for the problem (e.g., file path).
/// * `parse_time` - The time taken to parse the CNF input.
fn solve_and_report(cnf: Cnf, common: CommonOptions, label: Option<&str>, parse_time: Duration) {
    // Note: epoch::advance() is called inside solve_cdcl/solve_dpll before solving.
    // This advance is for memory stats *after* solving.
    epoch::advance().unwrap();

    let (sol, elapsed, solver_stats) = solve(cnf.clone(), common.debug, label, &common.solver);

    // Advance epoch again to ensure memory stats capture everything up to this point.
    epoch::advance().unwrap();

    // Read memory statistics using tikv_jemalloc_ctl.
    // These functions return byte counts.
    let allocated_bytes = stats::allocated::mib().unwrap().read().unwrap();
    let resident_bytes = stats::resident::mib().unwrap().read().unwrap();

    // Convert bytes to MiB for reporting.
    let allocated_mib = allocated_bytes as f64 / (1024.0 * 1024.0);
    let resident_mib = resident_bytes as f64 / (1024.0 * 1024.0);

    if common.verify {
        verify_solution(cnf.clone(), &sol);
    }

    if common.stats {
        print_stats(
            parse_time,
            elapsed,
            &cnf,
            &solver_stats,
            allocated_mib,
            resident_mib,
            common.print_solution,
            &sol,
        );
    }
}

/// Parses a textual representation of a CNF formula into a list of clauses.
///
/// Each line in the input string is treated as a clause.
/// Literals in a clause are space-separated integers.
/// A `0` terminates a clause.
/// Lines starting with 'c' (comment) or 'p' (problem line in DIMACS) are ignored.
///
/// # Arguments
/// * `input` - A string containing the CNF formula. Example: "1 -2 0\n-1 3 0".
///
/// # Returns
/// A `Vec<Vec<i32>>` where each inner vector represents a clause.
fn parse_textual_cnf(input: &str) -> Vec<Vec<i32>> {
    input
        .lines()
        .filter(|line| !line.trim().starts_with('c') && !line.trim().starts_with('p'))
        .map(|line| {
            line.split_whitespace()
                .map(str::parse::<i32>)
                .take_while(|res| *res != Ok(0)) // Clause ends with 0
                .map(Result::unwrap) // Assumes valid integers before 0
                .collect()
        })
        .collect_vec()
}

/// Helper function to print a single statistic line in a formatted table row.
///
/// # Arguments
/// * `label` - The description of the statistic.
/// * `value` - The value of the statistic, implementing `std::fmt::Display`.
fn stat_line(label: &str, value: impl std::fmt::Display) {
    println!("|  {:<28} {:>18}  |", label, value);
}

/// Helper function to print a statistic line that includes a rate (value/second).
///
/// # Arguments
/// * `label` - The description of the statistic.
/// * `value` - The raw count for the statistic.
/// * `elapsed` - The elapsed time in seconds, used to calculate the rate.
fn stat_line_with_rate(label: &str, value: usize, elapsed: f64) {
    let rate = if elapsed > 0.0 {
        value as f64 / elapsed
    } else {
        0.0
    };
    println!(
        "|  {:<20} {:>12} ({:>9.0}/sec)  |", // Adjusted formatting for rate
        label, value, rate
    );
}

/// Prints a summary of problem and search statistics.
///
/// # Arguments
/// * `parse_time` - Duration spent parsing the input.
/// * `elapsed` - Duration spent by the solver.
/// * `cnf` - The CNF formula.
/// * `s` - `SolutionStats` collected by the solver.
/// * `allocated` - Allocated memory in MiB.
/// * `resident` - Resident memory in MiB.
/// * `print_solution` - Flag indicating whether to print the solution model.
/// * `solutions` - The `Option<Solutions>` found by the solver.
#[allow(clippy::too_many_arguments)]
fn print_stats(
    parse_time: Duration,
    elapsed: Duration,
    cnf: &Cnf,
    s: &SolutionStats,
    allocated: f64, // Assumed to be in MiB
    resident: f64,  // Assumed to be in MiB
    print_solution: bool,
    solutions: &Option<Solutions>,
) {
    let elapsed_secs = elapsed.as_secs_f64();

    println!("\n=======================[ Problem Statistics ]=========================");
    stat_line("Parse time (s)", format!("{:.3}", parse_time.as_secs_f64()));
    stat_line(
        "Variables",
        if cnf.num_vars > 0 {
            cnf.num_vars - 1
        } else {
            0
        },
    ); // Max var ID is num_vars - 1
    stat_line("Clauses (original)", cnf.non_learnt_idx); // Number of non-learnt clauses
    stat_line("Literals (original)", cnf.lits.len()); // Total literals in original clauses

    println!("========================[ Search Statistics ]========================");
    stat_line("Learnt clauses", s.learnt_clauses);
    stat_line("Total clauses (incl. learnt)", cnf.clauses.len()); // cnf.clauses includes learnt ones if added there, or sum
    stat_line_with_rate("Conflicts", s.conflicts, elapsed_secs);
    stat_line_with_rate("Decisions", s.decisions, elapsed_secs);
    stat_line_with_rate("Propagations", s.propagations, elapsed_secs);
    stat_line_with_rate("Restarts", s.restarts, elapsed_secs);
    stat_line("Memory usage (MiB)", format!("{:.2}", allocated));
    stat_line("Resident memory (MiB)", format!("{:.2}", resident));
    stat_line("CPU time (s)", format!("{:.3}", elapsed_secs));
    println!("=====================================================================");

    if let Some(solutions_values) = solutions {
        if print_solution {
            println!("Solutions: {}", solutions_values);
        }
    }

    if solutions.is_some() {
        println!("\nSATISFIABLE");
    } else {
        println!("\nUNSATISFIABLE");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_textual_cnf_simple() {
        let input = "1 -2 0\n3 4 0";
        let expected = vec![vec![1, -2], vec![3, 4]];
        assert_eq!(parse_textual_cnf(input), expected);
    }

    #[test]
    fn test_parse_textual_cnf_with_comments_and_p_line() {
        let input = "c this is a comment\np cnf 2 2\n1 0\n-2 0";
        let expected = vec![vec![1], vec![-2]];
        assert_eq!(parse_textual_cnf(input), expected);
    }

    #[test]
    fn test_parse_textual_cnf_empty_lines() {
        // Empty lines (not starting with 'c' or 'p') result in empty clauses
        let input = "1 0\n\n-2 0";
        let expected = vec![vec![1], vec![], vec![-2]];
        assert_eq!(parse_textual_cnf(input), expected);
    }

    #[test]
    fn test_parse_textual_cnf_empty_input() {
        let input = "";
        let expected: Vec<Vec<i32>> = vec![]; // An empty line becomes an empty vec, but no lines means no vecs.
        assert_eq!(parse_textual_cnf(input), expected);
    }

    #[test]
    fn test_parse_textual_cnf_single_clause_no_newline() {
        let input = "1 2 3 0";
        let expected = vec![vec![1, 2, 3]];
        assert_eq!(parse_textual_cnf(input), expected);
    }

    #[test]
    fn test_parse_textual_cnf_clause_with_leading_space() {
        let input = "  1 2 0";
        let expected = vec![vec![1, 2]];
        assert_eq!(parse_textual_cnf(input), expected);
    }

    #[test]
    fn test_parse_textual_cnf_multiple_zeros_in_line() {
        // `take_while` stops at the first Ok(0)
        let input = "1 2 0 3 4 0";
        let expected = vec![vec![1, 2]];
        assert_eq!(parse_textual_cnf(input), expected);
    }

    // Note: Integration tests for CLI functionality would typically go in a separate `tests` directory
    // and use crates like `assert_cmd`. Since this is a single file, only unit tests are added here.
    // To add integration tests:
    // 1. Create `tests/cli.rs`.
    // 2. Use `std::process::Command` or `assert_cmd` to run the compiled binary.
    // 3. Prepare sample input files (DIMACS, Sudoku, Nonogram) in `tests/fixtures/`.
    // 4. Assert stdout, stderr, and exit codes.
    // Example (conceptual, needs `assert_cmd` and files):
    //
    // #[test]
    // fn test_cli_solve_dimacs_file() {
    //     use assert_cmd::Command;
    //     use std::fs;
    //
    //     // Create a dummy CNF file
    //     let cnf_content = "p cnf 2 2\n1 2 0\n-1 0\n";
    //     fs::write("tests/fixtures/sample_cli.cnf", cnf_content).unwrap();
    //
    //     let mut cmd = Command::cargo_bin(env!("CARGO_PKG_NAME")).unwrap();
    //     cmd.arg("tests/fixtures/sample_cli.cnf");
    //     cmd.assert()
    //        .success()
    //        .stdout(predicates::str::contains("SATISFIABLE"));
    //
    //     fs::remove_file("tests/fixtures/sample_cli.cnf").unwrap();
    // }
}
