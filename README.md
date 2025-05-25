# SATSolver - A Configurable SAT Solver in Rust

[![Build Status](https://img.shields.io/github/actions/workflow/status/YOUR_USERNAME/YOUR_REPONAME/rust.yml?branch=main)](https://github.com/YOUR_USERNAME/YOUR_REPONAME/actions)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

SATSolver is a command-line application written in Rust that implements a SAT (Boolean Satisfiability) solver based on the CDCL (Conflict-Driven Clause Learning) algorithm. It's designed to be configurable and includes modules for solving standard CNF (Conjunctive Normal Form) problems as well as specific applications like Sudoku puzzles by reducing them to SAT.

## Features

*   **CDCL Algorithm:** Implements the core Conflict-Driven Clause Learning algorithm for efficient SAT solving.
*   **DIMACS CNF Support:** Parses and solves SAT problems defined in the standard DIMACS CNF file format.
*   **Textual CNF Input:** Accepts CNF formulas directly as command-line arguments.
*   **Sudoku Solver:**
    *   Parses Sudoku puzzles from text files.
    *   Encodes Sudoku constraints into CNF.
    *   Solves the puzzle using the SAT solver.
    *   Decodes the SAT solution back into a solved Sudoku grid.
    *   Optionally exports the generated CNF in DIMACS format.
*   **Configurable Solver Components:** Uses a trait-based system (`SolverConfig`) allowing different implementations for:
    *   Literal Representation (`Literal`)
    *   Assignment Tracking (`Assignment`)
    *   Variable Selection Heuristics (`VariableSelector`, e.g. VSIDS)
    *   Unit Propagation (`Propagator`, e.g. Watched Literals)
    *   Restart Strategies (`Restarter`, e.g. Luby sequence)
    *   Clause Management (`ClauseManager`, e.g. LBD-based)
*   **Performance Statistics:** Reports detailed statistics like conflicts, decisions, propagations, restarts, timing, and memory usage.
*   **Solution Verification:** Includes an option to verify the correctness of found solutions.
*   **Memory Management:** Uses `tikv-jemallocator` for potentially better memory allocation performance and reporting accurate memory statistics.
*   **Command-Line Interface:** Easy-to-use CLI built with `clap`.

## Installation

[//]: # (1.  **Clone the repository:**)

[//]: # (    ```bash)

[//]: # (    git clone https://github.com/YOUR_USERNAME/YOUR_REPONAME.git)

[//]: # (    cd YOUR_REPONAME)

[//]: # (    ```)

[//]: # (    *&#40;Replace `YOUR_USERNAME/YOUR_REPONAME` with the actual URL&#41;*)

1. **Build the project:**
    For a release build (recommended for performance):
    ```bash
    cargo build --release
    ```
    The executable will be located at `target/release/satsolver`.

    For a debug build:
    ```bash
    cargo build
    ```
    The executable will be located at `target/debug/satsolver`.

    For installation, you can also use:
    ```bash
    cargo install --path .
    ```
    This will install the `sat_solver` binary globally, making it accessible from anywhere in your terminal.

## Usage

The solver can be invoked in several ways depending on the input type.

```bash
# General structure
sat_solver [GLOBAL OPTIONS] [COMMAND]

# Implicitly solve a DIMACS file
sat_solver <path/to/problem.cnf> [OPTIONS]

# Explicitly solve a DIMACS file
sat_solver file --path <path/to/problem.cnf> [OPTIONS]

# Solve CNF provided as text
sat_solver text --input "1 -2 0\n-1 3 0\n2 -3 0" [OPTIONS]

# Solve a Sudoku puzzle
sat_solver sudoku --path <path/to/sudoku.txt> [OPTIONS]
```

### Common Options

These options can be used with most commands:

*   `-d, --debug`: Enable detailed debug output during solving.
*   `-v, --verify`: Verify the solution after solving (default: true). Use `--no-verify` to disable.
*   `-s, --stats`: Print performance statistics (default: true). Use `--no-stats` to disable.
*   `-p, --print-solution`: Print the satisfying assignment if found (default: false).
*   `--help`: Show help information.
*   `--version`: Show version information.

### Examples

1.  **Solve a DIMACS file (`example.cnf`) and print stats:**
    ```bash
    sat_solver example.cnf
    # or
    sat_solver file --path example.cnf
    ```

2. **Solve inline CNF text and print the solution:**
    ```bash
    ./target/release/satsolver text --input "1 2 0\n-1 0\n-2 0" -p
    ```
    *(Note: Input string uses `\n` for newlines if necessary in your shell)*

3. **Solve a Sudoku puzzle (`puzzle.sudoku`) and print the solution:**
    ```bash
    sat_solver sudoku --path puzzle.sudoku -p
    ```

4. **Solve a Sudoku puzzle and export its CNF representation:**
    ```bash
    sat_solver sudoku --path puzzle.sudoku --export-dimacs
    # This will create puzzle.sudoku.cnf
    ```

## Solver Configuration

The solver's behavior is determined by the components defined in a `SolverConfig` implementation. The `DefaultConfig` uses:

*   `Literal`: `PackedLiteral` (an efficient representation for literals)
*   `LiteralStorage`: `SmallVec<[PackedLiteral; 8]>` (optimises storage for small clauses)
*   `Assignment`: `VecAssignment` (standard vector-based assignment tracking)
*   `VariableSelector`: `Vsids` (Variable State Independent Decaying Sum heuristic)
*   `Propagator`: `WatchedLiterals` (efficient unit propagation)
*   `Restarter`: `Luby<2>` (Luby sequence based restarts)
*   `ClauseManager`: `LbdClauseManagement` (Literal Block Distance based clause deletion)

While the current command-line interface uses `DefaultConfig`, the underlying structure allows for creating different configurations by implementing the `SolverConfig` trait and associated component traits.

## Input Formats

### DIMACS CNF (`.cnf`)

The standard format for SAT problems:

*   Lines starting with `c` are comments.
*   A single problem line: `p cnf <num_vars> <num_clauses>`
*   Clause lines: space-separated integers representing literals (positive for variable, negative for negated variable), ending with `0`.

Example:
```
c Example DIMACS file
p cnf 3 3
1 -2 0
-1 3 0
2 -3 0
```


### Sudoku (`.txt`, `.sudoku`, etc.)

A text file representing the 9x9 grid:

*   Use digits `1` through `9` for pre-filled cells.
*   Use `0` for empty cells.
*   Whitespace between characters is usually ignored.

Example:
```
5 3 0 0 7 0 0 0 0
6 0 0 1 9 5 0 0 0
0 9 8 0 0 0 0 6 0
0 0 0 0 4 0 8 0 3
0 0 0 0 0 0 0 0 0
0 0 0 0 0 0 0 2 8
0 0 0 0 6 0 0 0 0
0 0 0 0 0 0 0 0 0
```


## Output and Statistics

Upon completion, the solver will output:

1.  **(Optional)** Debug information if `-d` is enabled.
2.  Parsing information (for Sudoku/Nonogram).
3.  Solver progress/status (e.g. "Solving: <filename>").
4.  **(Optional)** Verification result if `--verify` is enabled.
5.  **(Optional)** Statistics if `--stats` is enabled (see below).
6.  **(Optional)** The solution assignment (list of true literals) if `-p` is enabled and the problem is SAT.
7.  The final result: `SATISFIABLE` or `UNSATISFIABLE`.
8.  (Sudoku/Nonogram) The decoded solution grid if SAT.

### Statistics Block (`--stats`)

The statistics block includes:
*   `conflicts`: Number of conflicts encountered.
*   `decisions`: Number of decisions made.
*  `propagations`: Number of propagations performed.
*  `restarts`: Number of restarts performed.
*  `time`: Total time taken for solving (in seconds).
*  `memory`: Memory usage (in bytes).
*  `solution`: The satisfying assignment (if found).
*  `verification`: Verification result (if enabled).
*  `exported_cnf`: Path to the exported CNF file (if applicable).

## Development

*   **Code Structure:**
    *   `src/main.rs`: CLI parsing and main application logic.
    *   `src/sat/`: Core SAT solver implementation (CDCL, CNF, components).
    *   `src/sudoku/`: Sudoku parsing, CNF encoding, and solution decoding.
    *   `src/smt/`: (Potentially for future SMT extensions - currently minimal).
*   **Testing:** Run tests with `cargo test`.
*   **Dependencies:** Key dependencies include `clap`, `itertools`, `tikv-jemallocator`, `tikv-jemalloc-ctl`, `rustc_hash`, `smallvec`.
