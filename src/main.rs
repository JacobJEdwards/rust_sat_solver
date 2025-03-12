use crate::sat::assignment::HashMapAssignment;
use crate::sat::assignment::VecAssignment;
use crate::sat::dimacs::parse_file;
use crate::sat::solver::Solver;
use crate::sat::cdcl::State;
use crate::sat::variable_selection::RandomOrder;
use crate::sudoku::solver::{Board, Sudoku, EXAMPLE_NINE};
use std::hint::black_box;

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
        let cnf = parse_file(&file).unwrap();
        let mut state: State = State::new(cnf.clone());
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
        let mut state: State<VecAssignment, RandomOrder> = Solver::new(cnf.clone());

        // state.add_preprocessor(TautologyElimination).add_preprocessor(SubsumptionElimination);

        let time = std::time::Instant::now();
        let sol = state.solve();

        println!("{:?}", sol);
        println!("time: {:?}", time.elapsed());

        if let Some(sol) = sol {
            let verify = cnf.verify(&sol);

            println!("verifying solution: {:?}", verify);

            if !verify {
                panic!("failed to verify solution");
            }
        }
    }
}
