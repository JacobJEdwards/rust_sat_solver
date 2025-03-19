use criterion::{criterion_group, criterion_main, Criterion};
use sat_solver::sat::assignment::{Assignment, HashMapAssignment, VecAssignment};
use sat_solver::sat::cdcl::Cdcl;
use sat_solver::sat::preprocessing::{
    Preprocessor, PureLiteralElimination, SubsumptionElimination, TautologyElimination,
};
use sat_solver::sat::restarter::{Exponential, Geometric, Linear, Luby, Never, Restarter};
use sat_solver::sat::solver::Solver;
use sat_solver::sat::variable_selection::{FixedOrder, RandomOrder, VariableSelection, Vsids};
use sat_solver::sudoku::solver::{Board, Sudoku, EXAMPLE_SIXTEEN};
use std::hint::black_box;
use std::time::Duration;
use sat_solver::sat::literal::{DoubleLiteral, Literal, PackedLiteral, StructLiteral};

fn bench_sudoku(c: &mut Criterion) {
    let board = EXAMPLE_SIXTEEN
        .iter()
        .map(|x| x.to_vec())
        .collect::<Vec<_>>();

    let sudoku = Sudoku::new(Board::from(board));
    let cnf = sudoku.to_cnf();

    c.bench_function("sudoku - vec assignment", |b| {
        b.iter(|| {
            let mut state: Cdcl<VecAssignment, Vsids> = Solver::new(cnf.clone());
            let sol = state.solve();
            black_box(sol);
        })
    });

    c.bench_function("sudoku - hash map assignment", |b| {
        b.iter(|| {
            let mut state: Cdcl<HashMapAssignment, Vsids> = Solver::new(cnf.clone());
            let sol = state.solve();
            black_box(sol);
        })
    });
}

fn solve_3sat<A: Assignment, V: VariableSelection, R: Restarter, L: Literal>() {
    for i in 1..1000 {
        let file = format!("data/uf20-91/uf20-0{}.cnf", i);
        let cnf = sat_solver::sat::dimacs::parse_file(&file).unwrap();
        let mut state: Cdcl<A, V, R, L> = Solver::new(cnf.clone());
        let sol = state.solve();
        black_box(sol);
    }
}

fn solve_graph_colouring<A: Assignment, V: VariableSelection, R: Restarter, L: Literal>() {
    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}.cnf", i);
        let cnf = sat_solver::sat::dimacs::parse_file(&file).unwrap();
        let mut state: Cdcl<A, V, R, L> = Solver::new(cnf.clone());
        let sol = state.solve();
        black_box(sol);
    }
}

fn solve_graph_colouring_with_preprocessors(
    tautology_elimination: bool,
    pure_literal: bool,
    subsumption_elimination: bool,
) {
    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}.cnf", i);
        let cnf = sat_solver::sat::dimacs::parse_file(&file).unwrap();

        let mut state: Cdcl<VecAssignment, Vsids, Luby> = Solver::new(cnf.clone());

        if tautology_elimination {
            state.add_preprocessor(TautologyElimination);
        }
        if pure_literal {
            state.add_preprocessor(PureLiteralElimination);
        }
        if subsumption_elimination {
            state.add_preprocessor(SubsumptionElimination);
        }

        let sol = state.solve();
        black_box(sol);
    }
}

fn bench_3sat(c: &mut Criterion) {
    let mut cnfs = Vec::new();
    for i in 1..1000 {
        let file = format!("data/uf20-91/uf20-0{}.cnf", i);
        match sat_solver::sat::dimacs::parse_file(&file) {
            Ok(cnf) => cnfs.push(cnf),
            Err(e) => eprintln!("Failed to parse {}: {}", file, e),
        }
    }

    let mut group = c.benchmark_group("3sat - restarter");
    group.sample_size(100);
    group.measurement_time(Duration::from_secs(20));

    group.bench_function("Luby", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<VecAssignment, Vsids, Luby, DoubleLiteral> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Geometric", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<VecAssignment, Vsids, Geometric, DoubleLiteral> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Linear", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<VecAssignment, Vsids, Linear, DoubleLiteral> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Exponential", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<VecAssignment, Vsids, Exponential, DoubleLiteral> = Solver::new(cnf.clone());black_box(state.solve());
            }
        })
    });

    group.bench_function("Never", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<VecAssignment, Vsids, Never, DoubleLiteral> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });
}

fn bench_graph_colouring(c: &mut Criterion) {
    let mut group = c.benchmark_group("graph_colouring - literal layout");
    group.sample_size(100);
    group.measurement_time(Duration::from_secs(20));

    let mut cnfs = Vec::new();

    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}.cnf", i);
        match sat_solver::sat::dimacs::parse_file(&file) {
            Ok(cnf) => cnfs.push(cnf),
            Err(e) => eprintln!("Failed to parse {}: {}", file, e),
        }
    }

    group.bench_function("Packed", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<HashMapAssignment, Vsids, Luby, PackedLiteral> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    let mut cnfs = Vec::new();

    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}.cnf", i);
        match sat_solver::sat::dimacs::parse_file(&file) {
            Ok(cnf) => cnfs.push(cnf),
            Err(e) => eprintln!("Failed to parse {}: {}", file, e),
        }
    }

    group.bench_function("Doubled", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<HashMapAssignment, Vsids, Luby, DoubleLiteral> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    let mut cnfs = Vec::new();

    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}.cnf", i);
        match sat_solver::sat::dimacs::parse_file(&file) {
            Ok(cnf) => cnfs.push(cnf),
            Err(e) => eprintln!("Failed to parse {}: {}", file, e),
        }
    }

    group.bench_function("Struct", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<HashMapAssignment, Vsids, Luby, StructLiteral> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    let mut cnfs = Vec::new();

    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}.cnf", i);
        match sat_solver::sat::dimacs::parse_file(&file) {
            Ok(cnf) => cnfs.push(cnf),
            Err(e) => eprintln!("Failed to parse {}: {}", file, e),
        }
    }

    group.bench_function("Negated", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<HashMapAssignment, Vsids, Luby, DoubleLiteral> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.finish();
    
    let mut cnfs = Vec::new();

    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}.cnf", i);
        match sat_solver::sat::dimacs::parse_file(&file) {
            Ok(cnf) => cnfs.push(cnf),
            Err(e) => eprintln!("Failed to parse {}: {}", file, e),
        }
    }
    
    let mut group = c.benchmark_group("graph_colouring - restart strategy");
    group.sample_size(100);
    group.measurement_time(Duration::from_secs(20));

    group.bench_function("Luby", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<VecAssignment, Vsids, Luby> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Geometric", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<VecAssignment, Vsids, Geometric> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Linear", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<VecAssignment, Vsids, Linear> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Exponential", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<VecAssignment, Vsids, Exponential> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Never", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<VecAssignment, Vsids, Never> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.finish();

    let mut group = c.benchmark_group("graph_colouring - Variable selection");
    group.sample_size(100);
    group.measurement_time(Duration::from_secs(20));

    group.bench_function("Vsids", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<VecAssignment, Vsids, Luby> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Fixed Order", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<VecAssignment, FixedOrder, Luby> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Random Order", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<VecAssignment, RandomOrder, Luby> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.finish();

    let mut group = c.benchmark_group("graph_colouring - Assignment type");
    group.sample_size(100);
    group.measurement_time(Duration::from_secs(20));

    group.bench_function("Vec", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<VecAssignment, Vsids, Luby> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Hashmap", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<HashMapAssignment, Vsids, Luby> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.finish();


    let mut group = c.benchmark_group("graph_colouring - Preprocessing");
    group.sample_size(100);
    group.measurement_time(Duration::from_secs(20));
    
    let mut cnfs = Vec::new();

    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}.cnf", i);
        match sat_solver::sat::dimacs::parse_file(&file) {
            Ok(cnf) => cnfs.push(cnf),
            Err(e) => eprintln!("Failed to parse {}: {}", file, e),
        }
    }
    
    let cnfs_for_preprocessors = cnfs.clone();

    group.bench_function("Tautology", |b| {
        b.iter(|| {
            for cnf in &cnfs_for_preprocessors {
                let mut state: Cdcl<VecAssignment, Vsids, Luby> = Solver::new(cnf.clone());
                state.add_preprocessor(TautologyElimination);
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Pure Literal", |b| {
        b.iter(|| {
            for cnf in &cnfs_for_preprocessors {
                let mut state: Cdcl<VecAssignment, Vsids, Luby> = Solver::new(cnf.clone());
                state.add_preprocessor(PureLiteralElimination);
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Subsumption", |b| {
        b.iter(|| {
            for cnf in &cnfs_for_preprocessors {
                let mut state: Cdcl<VecAssignment, Vsids, Luby> = Solver::new(cnf.clone());
                state.add_preprocessor(SubsumptionElimination);
                black_box(state.solve());
            }
        })
    });
}

criterion_group!(benches, bench_graph_colouring);

criterion_main!(benches);
