use criterion::{criterion_group, criterion_main, Criterion};
use sat_solver::sat::assignment::{Assignment, HashMapAssignment, VecAssignment};
use sat_solver::sat::restarter::{Exponential, Geometric, Linear, Luby, Never, Restarter};
use sat_solver::sat::solver::Solver;
use sat_solver::sat::cdcl::State;
use sat_solver::sat::variable_selection::{VariableSelection, Vsids};
use sat_solver::sudoku::solver::{Board, Sudoku, EXAMPLE_SIXTEEN};
use std::hint::black_box;
use std::time::Duration;

fn bench_sudoku(c: &mut Criterion) {
    let board = EXAMPLE_SIXTEEN
        .iter()
        .map(|x| x.to_vec())
        .collect::<Vec<_>>();

    let sudoku = Sudoku::new(Board::from(board));
    let cnf = sudoku.to_cnf();

    c.bench_function("sudoku - vec assignment", |b| {
        b.iter(|| {
            let mut state: State<VecAssignment, Vsids> = Solver::new(cnf.clone());
            let sol = state.solve();
            black_box(sol);
        })
    });

    c.bench_function("sudoku - hash map assignment", |b| {
        b.iter(|| {
            let mut state: State<HashMapAssignment, Vsids> = Solver::new(cnf.clone());
            let sol = state.solve();
            black_box(sol);
        })
    });
}

fn solve_3sat<A: Assignment, V: VariableSelection, R: Restarter>() {
    for i in 1..1000 {
        let file = format!("data/uf20-91/uf20-0{}.cnf", i);
        let cnf = sat_solver::sat::dimacs::parse_file(&file).unwrap();
        let mut state: State<A, V, R> = Solver::new(cnf.clone());
        let sol = state.solve();
        black_box(sol);
    }
}

fn solve_graph_colouring<A: Assignment, V: VariableSelection, R: Restarter>() {
    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}", 1);
        let cnf = sat_solver::sat::dimacs::parse_file(&file).unwrap();
        let mut state: State<A, V, R> = Solver::new(cnf.clone());
        let sol = state.solve();
        black_box(sol);
    }
}

fn bench_3sat(c: &mut Criterion) {
    let mut group = c.benchmark_group("3sat");
    group.sample_size(80);
    group.measurement_time(Duration::from_secs(10));

    group.bench_function("Vec Vsids Luby", |b| {
        b.iter(|| solve_3sat::<VecAssignment, Vsids, Luby>())
    });

    group.bench_function("Vec Vsids Geometric", |b| {
        b.iter(|| solve_3sat::<VecAssignment, Vsids, Geometric>())
    });

    group.bench_function("Vec Vsids Linear", |b| {
        b.iter(|| solve_3sat::<VecAssignment, Vsids, Linear>())
    });

    group.bench_function("Vec Vsids Exponential", |b| {
        b.iter(|| solve_3sat::<VecAssignment, Vsids, Exponential>())
    });

    group.bench_function("Vec Vsids Never", |b| {
        b.iter(|| solve_3sat::<VecAssignment, Vsids, Never>())
    });
}

fn bench_graph_colouring(c: &mut Criterion) {
    let mut group = c.benchmark_group("graph_colouring");
    group.sample_size(80);
    group.measurement_time(Duration::from_secs(10));

    group.bench_function("Vec Vsids Luby", |b| {
        b.iter(|| solve_graph_colouring::<VecAssignment, Vsids, Luby>())
    });

    group.bench_function("Vec Vsids Geometric", |b| {
        b.iter(|| solve_graph_colouring::<VecAssignment, Vsids, Geometric>())
    });

    group.bench_function("Vec Vsids Linear", |b| {
        b.iter(|| solve_graph_colouring::<VecAssignment, Vsids, Linear>())
    });

    group.bench_function("Vec Vsids Exponential", |b| {
        b.iter(|| solve_graph_colouring::<VecAssignment, Vsids, Exponential>())
    });

    group.bench_function("Vec Vsids Never", |b| {
        b.iter(|| solve_graph_colouring::<VecAssignment, Vsids, Never>())
    });
}

criterion_group!(benches, bench_3sat);

criterion_main!(benches);
