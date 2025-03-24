use crate::sat::cnf::Cnf;
use crate::sat::cdcl::Cdcl;
use crate::sat::dimacs::parse_file;
use crate::sat::dpll::Dpll;
use crate::sat::literal::PackedLiteral;
use crate::sat::preprocessing::{BlockedClauseElimination, BoundedVariableElimination, HyperBinaryResolution, Preprocessor, PreprocessorChain, PureLiteralElimination, SubsumptionElimination, TautologyElimination};
use crate::sat::solver::{Solver};

mod nonogram;
mod sat;
mod smt;
mod sudoku;

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
        let cnf = parse_file::<PackedLiteral>(&file).unwrap();
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
        let cnf = parse_file::<PackedLiteral>(&file).unwrap();

        let time = std::time::Instant::now();
        let clauses = cnf.clauses;
        let clauses = SubsumptionElimination.preprocess(&clauses);
        let clauses = PureLiteralElimination.preprocess(&clauses);
        let clauses = TautologyElimination.preprocess(&clauses);
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
