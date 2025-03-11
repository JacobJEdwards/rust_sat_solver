use log::debug;
use sat_solver::sat::dimacs::parse_dimacs;
use crate::sat::assignment::VecAssignment;
use crate::sat::dimacs::parse_file;
use crate::sat::propagation::{PropagationQueue, PropagationStack};
use crate::sat::restarter::Geometric;
use crate::sat::state::State;
use crate::sat::solver::Solver;
use crate::sat::variable_selection::{RandomOrder, Vsids};
use crate::sudoku::solver::{Board, Sudoku, EXAMPLE_NINE, EXAMPLE_SIXTEEN, EXAMPLE_TWENTY_FIVE};

mod nonogram;
mod sat;
mod sudoku;
mod smt;

fn main() {
    let board = Board::new(EXAMPLE_NINE.iter().map(|r| r.to_vec()).collect());
    let sudoku = Sudoku::new(board);
    
    
    
    
    for i in 1..30 {
        let file = format!("uf20-91/uf20-0{}.cnf", i);
        let cnf = parse_file(&file).unwrap();
        let mut state: State<> = State::new(cnf.clone());
        
        let time = std::time::Instant::now();
        let sol = state.solve();
        
        println!("{:?}", sol);
        println!("time: {:?}", time.elapsed());
        
        if let Some(sol) = sol {
            println!("verifying solution: {:?}", cnf.verify(&sol));
        }
    }
    let file = "uf20-91/uf20-05.cnf";
    
    let cnf = parse_file(file).unwrap();
    // let cnf = sudoku.to_cnf();
    
    let mut state: State<VecAssignment, Vsids> = State::new(cnf.clone());
    
    let time = std::time::Instant::now();
    let sol = state.solve();
    
    println!("{:?}", sol);
    println!("time: {:?}", time.elapsed());
    
    if let Some(sol) = sol {
        println!("verifying solution: {:?}", cnf.verify(&sol));
    }
}
