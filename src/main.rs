use crate::sat::assignment::VecAssignment;
use crate::sat::cdcl::Cdcl;
use crate::sat::cnf::Cnf;
use crate::sat::dimacs::parse_file;
use crate::sat::dpll::Dpll;
use crate::sat::literal::{NegativeLiteral, PackedLiteral};
use crate::sat::phase_saving::AdaptiveSavedPhases;
use crate::sat::preprocessing::{
    BlockedClauseElimination, BoundedVariableElimination, HyperBinaryResolution, Preprocessor,
    PreprocessorChain, PureLiteralElimination, SubsumptionElimination, TautologyElimination,
};
use crate::sat::propagation::{UnitSearch, WatchedLiterals};
use crate::sat::restarter::Luby;
use crate::sat::solver::{Solver, SolverConfig};
use crate::sat::variable_selection::Vsids;

mod nonogram;
mod sat;
mod smt;
mod sudoku;

// macro for generating a new type that implements SolverConfig
// implements SolverConfig for the generated type

fn main() {
    // let board = Board::new(EXAMPLE_NINE.iter().map(|r| r.to_vec()).collect());
    // let sudoku = Sudoku::new(board);
    // let cnf = sudoku.to_cnf();
    //
    // let mut state: State = State::new(cnf.clone());
    //
    // let sol = state.solve();
    //
    // let sol = sol.unwrap();
    //
    // let verify = cnf.verify(&sol);
    //
    // let board = sudoku.decode_solution(&sol);

    // println!("{:?}", board);

    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}.cnf", i);
        let cnf = parse_file(&file).unwrap();
        let mut state: Cdcl = Solver::new(cnf.clone());
        let sol = state.solve();

        println!("{:?}", file);
        println!("{:?}", sol);

        if let Some(sol) = sol {
            let verify = cnf.verify(&sol);
            println!("verifying solution: {:?}", verify);

            if !verify {
                panic!("failed to verify solution");
            }
        }

        println!()
    }

    for i in 1..30 {
        let file = format!("data/uf20-91/uf20-0{}.cnf", i);
        let cnf = parse_file(&file).unwrap();

        let time = std::time::Instant::now();
        let clauses = cnf.clauses;
        // let clauses = BoundedVariableElimination.preprocess(&clauses);
        // let clauses = BlockedClauseElimination.preprocess(&clauses);
        // let clauses = HyperBinaryResolution.preprocess(&clauses);

        let cnf = Cnf::from(clauses);
        let mut state: Cdcl = Solver::new(cnf);

        let sol = state.solve();

        println!("{:?}", sol);
        println!("time: {:?}", time.elapsed());

        if let Some(sol) = sol {
            let verify = state.cnf.verify(&sol);

            println!("verifying solution: {:?}", verify);

            if !verify {
                panic!("failed to verify solution");
            }
        }
    }
}
