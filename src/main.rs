use crate::sat::cdcl::Cdcl;
use crate::sat::cnf::Cnf;
use crate::sat::dimacs::parse_file;
use crate::sat::solver::{DefaultConfig, SolutionStats, Solutions, Solver};
use clap::{Args, Parser, Subcommand};
use itertools::Itertools;
use std::time::Duration;
use tikv_jemalloc_ctl::{epoch, stats};
use crate::sat::dpll::Dpll;

mod nonogram;
mod sat;
mod smt;
mod sudoku;

#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

#[derive(Parser, Debug)]
#[command(name = "SATSolver", version, about = "A configurable SAT solver")]
struct Cli {
    #[arg(global = true)]
    path: Option<String>,

    #[clap(subcommand)]
    command: Option<Commands>,

    #[command(flatten)]
    common: CommonOptions,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// Solve a CNF file in DIMACS format
    File {
        /// Path to the DIMACS .cnf file
        #[arg(short, long)]
        path: String,

        #[command(flatten)]
        common: CommonOptions,
    },

    /// Solve a CNF formula provided as plain text
    Text {
        /// Literal CNF input as a string
        #[arg(short, long)]
        input: String,

        #[command(flatten)]
        common: CommonOptions,
    },

    /// Solve a Sudoku puzzle
    Sudoku {
        /// Path to the Sudoku file
        #[arg(short, long)]
        path: String,

        #[arg(short, long, default_value_t = false)]
        export_dimacs: bool,

        #[command(flatten)]
        common: CommonOptions,
    },

    /// Solve a Sudoku puzzle
    Nonogram {
        /// Path to the Sudoku file
        #[arg(short, long)]
        path: String,

        #[command(flatten)]
        common: CommonOptions,
    },
}

#[derive(Args, Debug, Default)]
struct CommonOptions {
    /// Enable debug output
    #[arg(short, long, default_value_t = false)]
    debug: bool,

    /// Enable verification
    #[arg(short, long, default_value_t = true)]
    verify: bool,

    /// Enable statistics
    #[arg(short, long, default_value_t = true)]
    stats: bool,

    /// Enable print solution
    #[arg(short, long, default_value_t = false)]
    print_solution: bool,

    /// Solver type
    #[arg(short, long, default_value_t = String::from("cdcl"))]
    solver: String,
}

fn main() {
    let cli = Cli::parse();

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
            let sudoku = sudoku::solver::parse_sudoku_file(&path);

            match sudoku {
                Ok(sudoku) => {
                    println!("Parsed Sudoku:\n{sudoku}");

                    let cnf = sudoku.to_cnf();

                    if export_dimacs {
                        let dimacs = cnf.to_string();
                        println!("DIMACS:\n{dimacs}");

                        let path_name = path.to_string();
                        let dimacs_path = format!("{}.cnf", path_name);
                        std::fs::write(&dimacs_path, dimacs).expect("Unable to write file");
                        println!("DIMACS written to: {dimacs_path}");
                    }

                    let parse_time = time.elapsed();
                    let (sol, elapsed, solver) = solve(cnf.clone(), common.debug, Some(&path), &common.solver);
                    let allocated = stats::allocated::mib().unwrap().read().unwrap() as f64;
                    let resident = stats::resident::mib().unwrap().read().unwrap() as f64;
                    let allocated = allocated / 1024.0 / 1024.0;
                    let resident = resident / 1024.0 / 1024.0;

                    if common.verify {
                        verify_solution(cnf.clone(), &sol);
                    }

                    if common.stats {
                        print_stats(
                            parse_time,
                            elapsed,
                            &cnf,
                            &solver,
                            allocated,
                            resident,
                            common.print_solution,
                            &sol
                        );
                    }

                    if let Some(sol) = sol {
                        let solution = sudoku.decode(&sol);
                        println!("Solution: {solution}");
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
            let nonogram = nonogram::solver::parse_nonogram_file(&path);
            match nonogram {
                Ok(nonogram) => {
                    println!("Parsed Nonogram:\n{nonogram}");

                    let cnf = nonogram.to_cnf();

                    let parse_time = time.elapsed();
                    let (sol, elapsed, solver) = solve(cnf.clone(), common.debug, Some(&path), &common.solver);
                    let allocated = stats::allocated::mib().unwrap().read().unwrap() as f64;
                    let resident = stats::resident::mib().unwrap().read().unwrap() as f64;
                    let allocated = allocated / 1024.0 / 1024.0;
                    let resident = resident / 1024.0 / 1024.0;

                    if common.verify {
                        verify_solution(cnf.clone(), &sol);
                    }

                    if common.stats {
                        print_stats(
                            parse_time,
                            elapsed,
                            &cnf,
                            &solver,
                            allocated,
                            resident,
                            common.print_solution,
                            &sol
                        );
                    }

                    if let Some(sol) = sol {
                        let solution = nonogram.decode(&sol);
                        for row in solution.iter() {
                            println!("{:?}", row);
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
            if cli.path.is_none() {
                eprintln!("No command provided. Use --help for more information.");
                std::process::exit(1);
            }
        }
    }
}
fn verify_solution(cnf: Cnf, sol: &Option<Solutions>) {
    if let Some(sol) = sol.clone() {
        let ok = cnf.verify(&sol);
        println!("Verified: {:?}", ok);
        if !ok {
            panic!("Solution failed verification!");
        }
    } else {
        println!("UNSAT");
    }
}

fn solve(cnf: Cnf, debug: bool, label: Option<&str>, solver_name: &str) -> (Option<Solutions>,
                                                                        Duration, SolutionStats) {
    if let Some(name) = label {
        println!("Solving: {:?}", name);
    }

    if debug {
        println!("CNF: {}", cnf);
        println!("Variables: {}", cnf.num_vars);
        println!("Clauses: {}", cnf.clauses.len());
        println!("Literals: {}", cnf.lits.len());
    }

    if solver_name.to_lowercase() == "dpll" {
        return solve_dpll(cnf, debug);
    }

    if solver_name.to_lowercase() == "cdcl" {
        return solve_cdcl(cnf, debug);
    }

    panic!("Unknown solver name {}", solver_name);
}

fn solve_cdcl(cnf: Cnf, debug: bool) -> (Option<Solutions>, Duration, SolutionStats) {
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

fn solve_and_report(cnf: Cnf, common: CommonOptions, label: Option<&str>, parse_time: Duration) {
    epoch::advance().unwrap();

    let (sol, elapsed, solver) = solve(cnf.clone(), common.debug, label, &common.solver);

    epoch::advance().unwrap();

    let allocated = stats::allocated::mib().unwrap().read().unwrap() as f64;
    let resident = stats::resident::mib().unwrap().read().unwrap() as f64;

    let allocated = allocated / 1024.0 / 1024.0;
    let resident = resident / 1024.0 / 1024.0;

    if common.verify {
        verify_solution(cnf.clone(), &sol);
    }

    if common.stats {
        print_stats(
            parse_time,
            elapsed,
            &cnf,
            &solver,
            allocated,
            resident,
            common.print_solution,
            &sol
        );
    }
}

fn parse_textual_cnf(input: &str) -> Vec<Vec<i32>> {
    input
        .lines()
        .filter(|line| !line.trim().starts_with('c') && !line.trim().starts_with('p'))
        .map(|line| {
            line.split_whitespace()
                .map(str::parse::<i32>)
                .take_while(|res| *res != Ok(0))
                .map(Result::unwrap)
                .collect()
        })
        .collect_vec()
}

fn stat_line(label: &str, value: impl std::fmt::Display) {
    println!("|  {:<28} {:>18}  |", label, value);
}

fn stat_line_with_rate(label: &str, value: usize, elapsed: f64) {
    println!(
        "|  {:<20} {:>12} ({:.0}/sec)  |",
        label,
        value,
        value as f64 / elapsed
    );
}

#[allow(clippy::too_many_arguments)]
fn print_stats(
    parse_time: Duration,
    elapsed: Duration,
    cnf: &Cnf,
    s: &SolutionStats,
    allocated: f64,
    resident: f64,
    print_solution: bool,
    solutions: &Option<Solutions>,
) {
    let elapsed_secs = elapsed.as_secs_f64();

    println!("\n=======================[ Problem Statistics ]=========================");
    stat_line("Parse time (s)", format!("{:.3}", parse_time.as_secs_f64()));
    stat_line("Variables", cnf.num_vars - 1);
    stat_line("Clauses", cnf.non_learnt_idx);
    stat_line("Literals", cnf.lits.len());

    println!("========================[ Search Statistics ]========================");
    stat_line("Learnt clauses", s.learnt_clauses);
    stat_line("Total clauses", cnf.clauses.len() + s.learnt_clauses);
    stat_line_with_rate("Conflicts", s.conflicts, elapsed_secs);
    stat_line_with_rate("Decisions", s.decisions, elapsed_secs);
    stat_line_with_rate("Propagations", s.propagations, elapsed_secs);
    stat_line_with_rate("Restarts", s.restarts, elapsed_secs);
    stat_line("Memory usage (MB)", allocated);
    stat_line("Resident memory (MB)", resident);
    stat_line("CPU time (s)", elapsed_secs);
    println!("=====================================================================");

    if let Some(solutions) = solutions {
        if print_solution {
            println!("Solutions: {}", solutions);
        }
    }

    if solutions.is_some() {
        println!("\nSATISFIABLE");
    } else {
        println!("\nUNSATISFIABLE");
    }
}
