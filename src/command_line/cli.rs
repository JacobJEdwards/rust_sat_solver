#![allow(dead_code, clippy::cast_precision_loss)]

use crate::sat::assignment::{AssignmentImpls, AssignmentType};
use crate::sat::cdcl::Cdcl;
use crate::sat::clause_management::{
    ClauseManagement, ClauseManagementImpls, LbdClauseManagement, NoClauseManagement,
};
use crate::sat::clause_storage::{LiteralStorage, LiteralStorageImpls, LiteralStorageType};
use crate::sat::cnf::Cnf;
use crate::sat::dimacs::parse_file;
use crate::sat::dpll::Dpll;
use crate::sat::literal::{Literal, LiteralImpls, LiteralType};
use crate::sat::propagation::{PropagatorImpls, PropagatorType};
use crate::sat::restarter::{RestarterImpls, RestarterType};
use crate::sat::solver::{
    DynamicConfig, SolutionStats, Solutions, Solver, SolverImpls, SolverType,
};
use crate::sat::variable_selection::{VariableSelectionImpls, VariableSelectionType};
use crate::{nonogram, sudoku};
use clap::{Args, Parser, Subcommand};
use std::path::PathBuf;
use std::time::Duration;
use tikv_jemalloc_ctl::{epoch, stats};

/// Defines the command-line interface for the sat solver application.
///
/// Uses `clap` for parsing arguments.
#[derive(Parser, Debug)]
#[command(name = "sat_solver", version, about = "A configurable SAT solver")]
pub(crate) struct Cli {
    /// An optional global path argument. If provided without a subcommand,
    /// it's treated as the path to a DIMACS .cnf file to solve.
    /// value hint for directory or file path ending with `.cnf`.
    #[arg(global = true)]
    pub path: Option<PathBuf>,

    /// Specifies the subcommand to execute (e.g. `file`, `text`, `sudoku`, `nonogram`).
    #[clap(subcommand)]
    pub command: Option<Commands>,

    /// Common options applicable to all commands.
    #[command(flatten)]
    pub common: CommonOptions,
}

/// Enumerates the available subcommands for the sat solver.
#[derive(Subcommand, Debug)]
pub(crate) enum Commands {
    /// Solve a CNF file in DIMACS format.
    File {
        /// Path to the DIMACS .cnf file.
        #[arg(long)]
        path: PathBuf,

        /// Common options for this subcommand.
        #[command(flatten)]
        common: CommonOptions,
    },

    /// Solve a CNF formula provided as plain text.
    Text {
        /// Literal CNF input as a string (e.g. "1 -2 0\n2 3 0").
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
        #[arg(long)]
        path: PathBuf,

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
        #[arg(long)]
        path: PathBuf,

        /// Common options for this subcommand.
        #[command(flatten)]
        common: CommonOptions,
    },

    /// Generate shell completion scripts.
    Completions {
        /// The shell to generate completions for.
        #[arg(value_enum)]
        shell: clap_complete::Shell,
    },
}

/// Defines common command-line options shared across different subcommands.
#[derive(Args, Debug, Default, Clone)]
#[allow(clippy::struct_excessive_bools)]
pub(crate) struct CommonOptions {
    /// Enable debug output, providing more verbose logging during the solving process.
    #[arg(short, long, default_value_t = false)]
    pub(crate) debug: bool,

    /// Enable verification of the found solution. If a solution is found, it's checked against the original CNF.
    #[arg(short, long, default_value_t = true)]
    pub(crate) verify: bool,

    /// Enable printing of performance and problem statistics after solving.
    #[arg(short, long, default_value_t = true)]
    pub(crate) stats: bool,

    /// Enable printing of the satisfying assignment (model) if the formula is satisfiable.
    #[arg(short, long, default_value_t = false)]
    pub(crate) print_solution: bool,

    /// Specifies the SAT solver algorithm to use.
    /// Supported values are "cdcl" (Conflict-Driven Clause Learning) and "dpll" (Davis-Putnam-Logemann-Loveland).
    #[arg(long, default_value_t = SolverType::Cdcl)]
    solver: SolverType,

    /// Disable clause management, which may affect the solver's performance and memory usage.
    #[arg(long, default_value_t = false)]
    no_clause_management: bool,

    #[arg(long, default_value_t = RestarterType::Luby)]
    restart_strategy: RestarterType,

    #[arg(long, default_value_t = VariableSelectionType::Vsids)]
    variable_selection: VariableSelectionType,

    #[arg(long, default_value_t = LiteralStorageType::SmallVec)]
    literal_storage: LiteralStorageType,

    #[arg(long, default_value_t = AssignmentType::Vec)]
    assignment: AssignmentType,

    #[arg(long, default_value_t = PropagatorType::WatchedLiterals)]
    propagator: PropagatorType,

    #[arg(long, default_value_t = LiteralType::Double)]
    literals: LiteralType,
}

/// Converts the `CommonOptions` into the specific implementations required by the solver.
pub(crate) fn get_solver_parts<L: Literal, S: LiteralStorage<L>>(
    common: &CommonOptions,
    cnf: &Cnf<L, S>,
) -> (
    AssignmentImpls,
    ClauseManagementImpls<10>,
    PropagatorImpls<LiteralImpls, LiteralStorageImpls<LiteralImpls, 12>, AssignmentImpls>,
    VariableSelectionImpls,
    RestarterImpls<3>,
) {
    let manager = if common.no_clause_management {
        ClauseManagementImpls::NoClauseManagement(NoClauseManagement::new(&cnf.clauses))
    } else {
        ClauseManagementImpls::LbdActivityClauseManagement(LbdClauseManagement::new(&cnf.clauses))
    };
    let cnf1: Cnf<LiteralImpls, LiteralStorageImpls<LiteralImpls, 12>> = cnf.convert();
    let propagator = common.propagator.to_impl(&cnf1);

    (
        common.assignment.to_impl(cnf.num_vars),
        manager,
        propagator,
        common
            .variable_selection
            .to_impl(cnf.num_vars, &cnf.lits, &cnf.clauses),
        common.restart_strategy.to_impl(),
    )
}

pub(crate) fn get_solver<L: Literal, S: LiteralStorage<L>>(
    common: &CommonOptions,
    cnf: &Cnf<L, S>,
) -> SolverImpls<DynamicConfig> {
    let (assignment, manager, propagator, selector, restarter) = get_solver_parts(common, cnf);

    match common.solver {
        SolverType::Cdcl => SolverImpls::Cdcl(Box::from(Cdcl::<DynamicConfig>::from_parts(
            cnf.clone(),
            assignment,
            manager,
            propagator,
            restarter,
            selector,
        ))),
        SolverType::Dpll => SolverImpls::Dpll(Box::from(Dpll::<DynamicConfig>::from_parts(
            cnf.clone(),
            assignment,
            manager,
            propagator,
            restarter,
            selector,
        ))),
    }
}

/// Solves a directory of CNF files.
/// This function iterates over all `.cnf` files in the directory, parses each file,
/// solves it, and reports the results.
///
/// # Arguments
/// * `path` - The path to the directory containing CNF files.
/// * `common` - Common options for the solver, such as debug mode, verification, and statistics.
///
/// # Panics
/// If the provided path is not a directory or if any file cannot be read or parsed.
pub(crate) fn solve_dir(path: &PathBuf, common: &CommonOptions) -> Result<(), String> {
    if !path.is_dir() {
        eprintln!("Provided path is not a directory: {}", path.display());
        std::process::exit(1);
    }

    for entry in walkdir::WalkDir::new(path)
        .into_iter()
        .filter_map(Result::ok)
    {
        let file_path = entry.path().to_path_buf();
        if file_path.extension().is_some_and(|ext| ext == "sudoku") {
            solve_sudoku(&file_path, false, common)?;
            continue;
        }

        if file_path.extension().is_none_or(|ext| ext != "cnf") {
            eprintln!("Skipping non-CNF file: {}", file_path.display());
            continue;
        }

        if !file_path.is_file() {
            eprintln!("Skipping non-file entry: {}", file_path.display());
            continue;
        }

        if !file_path.exists() {
            eprintln!("File does not exist: {}", file_path.display());
            continue;
        }

        let time = std::time::Instant::now();
        let result = parse_file(&file_path);
        if let Err(e) = result {
            return Err(e.to_string());
        }
        let cnf = result.unwrap();
        let elapsed = time.elapsed();

        solve_and_report(&cnf, common, Some(&file_path), elapsed);
    }

    Ok(())
}

/// Verifies a given solution (`sol`) against a CNF formula (`cnf`).
///
/// Prints whether the verification was successful. If verification fails, it panics.
/// If `sol` is `None` (indicating UNSAT), it prints "UNSAT".
///
/// # Arguments
/// * `cnf` - The CNF formula to verify against.
/// * `sol` - An `Option<Solutions>` representing the model found by the solver.
pub(crate) fn verify_solution(cnf: &Cnf, sol: Option<&Solutions>) {
    if let Some(sol_values) = sol {
        let ok = cnf.verify(sol_values);
        println!("Verified: {ok:?}");
        assert!(ok, "Solution failed verification!");
    } else {
        println!("UNSAT");
    }
}

/// Solves a CNF formula using the specified solver.
///
/// # Arguments
/// * `cnf` - The CNF formula to solve.
/// * `debug` - Boolean flag to enable debug printing.
/// * `label` - An optional label for the problem (e.g. file path), used in debug output.
/// * `solver_name` - The name of the solver to use ("dpll" or "cdcl").
///
/// # Returns
/// A tuple containing:
/// * `Option<Solutions>`: The solution (model) if found, otherwise `None`.
/// * `Duration`: The time taken to solve the formula.
/// * `SolutionStats`: Statistics collected during the solving process.
///
/// # Panics
/// If `solver_name` is not "dpll" or "cdcl".
pub(crate) fn solve(
    cnf: &Cnf,
    debug: bool,
    label: Option<&PathBuf>,
    common_options: &CommonOptions,
) -> (Option<Solutions>, Duration, SolutionStats) {
    if let Some(name) = label {
        println!("Solving: {}", name.display());
    }

    if debug {
        println!("CNF: {cnf}");
        println!("Variables: {}", cnf.num_vars);
        println!("Clauses: {}", cnf.clauses.len());
        println!("Literals: {}", cnf.lits.len());
    }

    solve_impl(cnf, common_options)
}

/// Solves a CNF formula using the CDCL solver.
///
/// # Arguments
/// * `cnf` - The CNF formula to solve.
/// * `debug` - Boolean flag to enable debug printing.
///
/// # Returns
/// See `solve` function return type.
pub(crate) fn solve_impl(
    cnf: &Cnf,
    common_options: &CommonOptions,
) -> (Option<Solutions>, Duration, SolutionStats) {
    epoch::advance().unwrap();

    let time = std::time::Instant::now();

    let mut solver = get_solver(common_options, cnf);
    let sol = solver.solve();

    let elapsed = time.elapsed();

    if common_options.debug {
        println!("Solution: {sol:?}");
        println!("Time: {elapsed:?}");
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
/// * `label` - An optional label for the problem (e.g. file path).
/// * `parse_time` - The time taken to parse the CNF input.
pub(crate) fn solve_and_report(
    cnf: &Cnf,
    common: &CommonOptions,
    label: Option<&PathBuf>,
    parse_time: Duration,
) {
    epoch::advance().unwrap();

    let (sol, elapsed, solver_stats) = solve(cnf, common.debug, label, common);

    epoch::advance().unwrap();

    let allocated_bytes = stats::allocated::mib().unwrap().read().unwrap();
    let resident_bytes = stats::resident::mib().unwrap().read().unwrap();

    let allocated_mib = allocated_bytes as f64 / (1024.0 * 1024.0);
    let resident_mib = resident_bytes as f64 / (1024.0 * 1024.0);

    if common.verify {
        verify_solution(cnf, Option::from(&sol));
    }

    if common.stats {
        print_stats(
            parse_time,
            elapsed,
            cnf,
            &solver_stats,
            allocated_mib,
            resident_mib,
            common.print_solution,
            Option::from(&sol),
        );
    }
}

/// Helper function to print a single statistic line in a formatted table row.
///
/// # Arguments
/// * `label` - The description of the statistic.
/// * `value` - The value of the statistic, implementing `std::fmt::Display`.
pub(crate) fn stat_line(label: &str, value: impl std::fmt::Display) {
    println!("|  {label:<28} {value:>18}  |");
}

/// Helper function to print a statistic line that includes a rate (value/second).
///
/// # Arguments
/// * `label` - The description of the statistic.
/// * `value` - The raw count for the statistic.
/// * `elapsed` - The elapsed time in seconds, used to calculate the rate.
pub(crate) fn stat_line_with_rate(label: &str, value: usize, elapsed: f64) {
    let rate = if elapsed > 0.0 {
        value as f64 / elapsed
    } else {
        0.0
    };
    println!("|  {label:<20} {value:>12} ({rate:>9.0}/sec)  |");
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
pub(crate) fn print_stats(
    parse_time: Duration,
    elapsed: Duration,
    cnf: &Cnf,
    s: &SolutionStats,
    allocated: f64,
    resident: f64,
    print_solution: bool,
    solutions: Option<&Solutions>,
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
    );
    stat_line("Clauses (original)", cnf.non_learnt_idx);
    stat_line("Literals (original)", cnf.lits.len());

    println!("========================[ Search Statistics ]========================");
    stat_line("Learnt clauses", s.learnt_clauses);
    stat_line("Total clauses (incl. learnt)", cnf.clauses.len());
    stat_line_with_rate("Conflicts", s.conflicts, elapsed_secs);
    stat_line_with_rate("Decisions", s.decisions, elapsed_secs);
    stat_line_with_rate("Propagations", s.propagations, elapsed_secs);
    stat_line_with_rate("Restarts", s.restarts, elapsed_secs);
    stat_line("Memory usage (MiB)", format!("{allocated:.2}"));
    stat_line("Resident memory (MiB)", format!("{resident:.2}"));
    stat_line("CPU time (s)", format!("{elapsed_secs:.3}"));
    println!("=====================================================================");

    if let Some(solutions_values) = solutions {
        if print_solution {
            println!("Solutions: {solutions_values}");
        }
    }

    if solutions.is_some() {
        println!("\nSATISFIABLE");
    } else {
        println!("\nUNSATISFIABLE");
    }
}

/// Solve a sudoku file.
///
/// # Errors
///
/// If the sudoku doesn't exist.
pub(crate) fn solve_sudoku(
    path: &PathBuf,
    export_dimacs: bool,
    common: &CommonOptions,
) -> Result<(), String> {
    if !path.exists() {
        return Err(format!("Sudoku file does not exist: {}", path.display()));
    }

    if !path.is_file() {
        return Err(format!("Provided path is not a file: {}", path.display()));
    }

    let time = std::time::Instant::now();
    let sudoku = sudoku::solver::parse_sudoku_file(path);

    match sudoku {
        Ok(sudoku) => {
            println!("Parsed Sudoku:\n{sudoku}");

            let cnf = sudoku.to_cnf();

            if export_dimacs {
                let dimacs = cnf.to_string();
                println!("DIMACS:\n{dimacs}");

                let path_name = path.display().to_string();
                let dimacs_path = format!("{path_name}.cnf");
                if let Err(e) = std::fs::write(&dimacs_path, dimacs) {
                    return Err(format!("Unable to write {dimacs_path}: {e}"));
                }
                println!("DIMACS written to: {dimacs_path}");
            }

            let parse_time = time.elapsed();
            let (sol, elapsed, solver_stats) = solve(&cnf, common.debug, Some(path), common);

            epoch::advance().unwrap();

            let allocated_bytes = stats::allocated::mib().unwrap().read().unwrap();
            let resident_bytes = stats::resident::mib().unwrap().read().unwrap();
            let allocated_mib = allocated_bytes as f64 / (1024.0 * 1024.0);
            let resident_mib = resident_bytes as f64 / (1024.0 * 1024.0);

            if common.verify {
                verify_solution(&cnf, Option::from(&sol));
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
                    Option::from(&sol),
                );
            }

            if let Some(sol_values) = sol {
                let solution_grid = sudoku.decode(&sol_values);
                println!("Solution: {solution_grid}");
            } else {
                println!("No solution found");
            }
        }
        Err(e) => {
            return Err(format!("Error parsing Sudoku file: {e}"));
        }
    }
    Ok(())
}

/// Solve a nonogram file.
///
/// # Errors
///
/// If the nonogram doesn't exist.
pub(crate) fn solve_nonogram(path: &PathBuf, common: &CommonOptions) -> Result<(), String> {
    if !path.exists() {
        return Err(format!("Nonogram file does not exist: {}", path.display()));
    }

    if !path.is_file() {
        return Err(format!("Provided path is not a file: {}", path.display()));
    }

    let time = std::time::Instant::now();
    let nonogram = nonogram::solver::parse_nonogram_file(path);
    match nonogram {
        Ok(nonogram) => {
            println!("Parsed Nonogram:\n{nonogram}");

            let cnf = nonogram.to_cnf();

            let parse_time = time.elapsed();
            let (sol, elapsed, solver_stats) = solve(&cnf, common.debug, Some(path), common);

            epoch::advance().unwrap();
            let allocated_bytes = stats::allocated::mib().unwrap().read().unwrap();
            let resident_bytes = stats::resident::mib().unwrap().read().unwrap();
            let allocated_mib = allocated_bytes as f64 / (1024.0 * 1024.0);
            let resident_mib = resident_bytes as f64 / (1024.0 * 1024.0);

            if common.verify {
                verify_solution(&cnf, Option::from(&sol));
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
                    Option::from(&sol),
                );
            }

            if let Some(sol_values) = sol {
                let solution_grid = nonogram.decode(&sol_values);
                for row in solution_grid {
                    println!("{row:?}");
                }
            } else {
                println!("No solution found");
            }
        }
        Err(e) => {
            return Err(format!("Error parsing nonogram file: {e}"));
        }
    }
    Ok(())
}
