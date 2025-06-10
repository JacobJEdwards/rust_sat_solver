#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
//! A parser for the DIMACS CNF (Conjunctive Normal Form) file format.
//!
//! The DIMACS CNF format is a standard text-based format for representing
//! boolean satisfiability problems. This module provides functions to parse
//! such files into an in-memory `Cnf` (Conjunctive Normal Form) structure.
//!
//! The format typically includes:
//! - Comment lines starting with 'c'.
//! - A problem line starting with 'p cnf <`num_variables`> <`num_clauses`>'.
//! - Clause lines, where each line represents a clause. Literals are represented
//!   by integers (positive for the variable, negative for its negation).
//!   Each clause line is terminated by a '0'.
//! - An optional '%' line to indicate end-of-data (used in competition data).
//!
//! This parser focuses on extracting the clause data.

use crate::sat::clause_storage::LiteralStorage;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use itertools::Itertools; // For `collect_vec`
use std::io::{self, BufRead};
use std::path::PathBuf;

/// Parses a DIMACS CNF file from a `BufRead` source.
///
/// This function is a convenience wrapper around `parse_dimacs`.
/// It reads the input from a string slice, which is useful for testing or
/// when the DIMACS data is available as a string.
///
/// # Type Parameters
/// * `L`: The `Literal` type to be used in the resulting `Cnf`.
/// * `S`: The `LiteralStorage` type for clauses in the resulting `Cnf`.
/// # Arguments
/// * `dimacs_text`: A string slice containing the DIMACS CNF data.
/// # Errors
/// - If parsing fails due to malformed input (e.g. non-integer literals, missing terminators).
pub fn parse_dimacs_text<L: Literal, S: LiteralStorage<L>>(
    dimacs_text: &str,
) -> Result<Cnf<L, S>, String> {
    let reader = io::Cursor::new(dimacs_text);
    parse_dimacs(reader)
}

/// Parses DIMACS formatted data from a `BufRead` source into a `Cnf` structure.
///
/// It reads the input line by line:
/// - Lines starting with 'c' (comments) or 'p' (problem line) are currently skipped without parsing their content.
/// - Lines starting with '%' or empty lines after the main content are treated as end-of-data markers.
/// - Other lines are treated as clause definitions. Each number on such a line is parsed as an `i32` literal.
///   The terminating '0' of a DIMACS clause line is filtered out.
///
/// # Type Parameters
///
/// * `R`: A type that implements `BufRead` (e.g. `io::BufReader<File>`).
/// * `L`: The `Literal` type to be used in the resulting `Cnf`.
/// * `S`: The `LiteralStorage` type for clauses in the resulting `Cnf`.
///
/// # Panics
///
/// - If reading a line from the `reader` fails (e.g. I/O error, invalid UTF-8).
/// - If parsing a literal string (e.g. "1", "-2") into an `i32` fails. This implies
///   a malformed DIMACS file if non-integer tokens appear where literals are expected.
///
/// # Returns
///
/// A `Cnf<L, S>` structure representing the parsed formula.
/// Or `None` if no clauses were found (e.g. empty file or only comments).
///
/// # Errors
/// Returns `()` if parsing fails due to malformed input (e.g. non-integer literals, missing terminators).
pub fn parse_dimacs<R: BufRead, L: Literal, S: LiteralStorage<L>>(
    reader: R,
) -> Result<Cnf<L, S>, String> {
    let mut lines = reader
        .lines()
        .map_while(Result::ok)
        .filter(|line| !line.is_empty());

    let mut clauses_dimacs: Vec<Vec<i32>> = Vec::new();

    for line_str in &mut lines {
        let mut parts = line_str.split_whitespace().peekable();

        match parts.peek() {
            Some(&"%") => break,
            None | Some(&"c" | &"p") => {}
            Some(_) => {
                let clause_literals: Vec<i32> = parts
                    .map(|s| {
                        s.parse::<i32>()
                            .unwrap_or_else(|e| panic!("Failed to parse literal '{s}' as i32: {e}"))
                    })
                    .filter(|&p| p != 0)
                    .collect_vec();

                if !clause_literals.is_empty() {
                    clauses_dimacs.push(clause_literals);
                }
            }
        }
    }
    Ok(Cnf::new(clauses_dimacs))
}

/// Parses a DIMACS CNF file specified by its path.
///
/// This is a convenience function that opens the file, wraps it in a `BufReader`,
/// and then calls `parse_dimacs`.
///
/// # Type Parameters
///
/// * `T`: The `Literal` type for the `Cnf`.
/// * `S`: The `LiteralStorage` type for the `Cnf`.
///
/// # Arguments
///
/// * `file_path`: A string slice representing the path to the DIMACS file.
///
/// # Errors
///
/// Returns `io::Result::Err` if the file cannot be opened or read (e.g. path does not exist,
/// permissions error). Panics from `parse_dimacs` (e.g. malformed content) will propagate.
///
/// # Returns
///
/// `io::Result::Ok(Cnf<T, S>)` if parsing is successful.
pub fn parse_file<T: Literal, S: LiteralStorage<T>>(file_path: &PathBuf) -> io::Result<Cnf<T, S>> {
    let file = std::fs::File::open(file_path)?;
    let reader = io::BufReader::new(file);
    let cnf: Cnf<T, S> = parse_dimacs(reader).map_err(|s| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("Failed to parse DIMACS file: {}, {s}", file_path.display()),
        )
    })?;
    if cnf.clauses.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("No clauses found in DIMACS file: {}", file_path.display()),
        ));
    }
    Ok(cnf)
}

/// Recursively finds all files in a directory and its subdirectories.
///
/// # Arguments
///
/// * `dir_path`: A string slice representing the path to the directory to scan.
///
/// # Errors
///
/// Returns `io::Result::Err` if there's an issue reading the directory or its entries
/// (e.g. path does not exist, permissions error).
///
/// # Panics
///
/// - If `entry.path().to_str()` returns `None` (i.e. the path is not valid UTF-8).
///
/// # Returns
///
/// `io::Result::Ok(Vec<String>)` containing the full paths of all files found.
#[allow(dead_code)]
pub fn get_all_files(dir_path: &str) -> io::Result<Vec<String>> {
    let mut files_found = Vec::new();

    for entry_result in std::fs::read_dir(dir_path)? {
        let entry = entry_result?;
        let path = entry.path();

        if path.is_file() {
            let path_str = path
                .to_str()
                .unwrap_or_else(|| panic!("Path contains non-UTF8 characters: {}", path.display()))
                .to_string();
            files_found.push(path_str);
        } else if path.is_dir() {
            let sub_dir_path_str = path.to_str().unwrap_or_else(|| {
                panic!(
                    "Subdirectory path contains non-UTF8 characters: {}",
                    path.display()
                )
            });
            let mut sub_files = get_all_files(sub_dir_path_str)?;
            files_found.append(&mut sub_files);
        }
    }

    Ok(files_found)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::literal::{DoubleLiteral, PackedLiteral};
    use std::io::Cursor;

    type TestCnf = Cnf<PackedLiteral, smallvec::SmallVec<[PackedLiteral; 8]>>;

    #[test]
    fn test_parse_simple_dimacs() {
        let dimacs_content = "c This is a comment\n\
                              p cnf 3 2\n\
                              1 -2 0\n\
                              2 3 0\n";
        let reader = Cursor::new(dimacs_content);
        let result = parse_dimacs(reader);
        assert!(result.is_ok(), "Parsing should succeed");
        let cnf: TestCnf = result.unwrap();

        assert_eq!(cnf.clauses.len(), 2, "Should parse 2 clauses");
        assert_eq!(cnf.num_vars, 3 + 1, "Number of variables mismatch");

        assert_eq!(cnf.clauses[0].len(), 2);
        let c1_lits: Vec<i32> = cnf.clauses[0]
            .iter()
            .map(Literal::to_i32)
            .sorted()
            .collect();
        assert_eq!(c1_lits, vec![-2, 1]);

        assert_eq!(cnf.clauses[1].len(), 2);
        let c2_lits: Vec<i32> = cnf.clauses[1]
            .iter()
            .map(Literal::to_i32)
            .sorted()
            .collect();
        assert_eq!(c2_lits, vec![2, 3]);
    }

    #[test]
    fn test_parse_dimacs_with_empty_lines_and_end_marker() {
        let dimacs_content = "p cnf 2 2\n\
                              \n\
                              1 0\n\
                              \n\
                              -2 0\n\
                              %\n\
                              c this should be ignored";
        let reader = Cursor::new(dimacs_content);
        let result = parse_dimacs(reader);
        assert!(result.is_ok(), "Parsing should succeed");
        let cnf: TestCnf = result.unwrap();

        assert_eq!(cnf.clauses.len(), 2);
        assert_eq!(cnf.num_vars, 2 + 1);
        assert_eq!(cnf.clauses[0].iter().next().unwrap().to_i32(), 1);
        assert_eq!(cnf.clauses[1].iter().next().unwrap().to_i32(), -2);
    }

    #[test]
    fn test_parse_dimacs_empty_clause() {
        let dimacs_content = "p cnf 1 1\n0\n";
        let reader = Cursor::new(dimacs_content);
        let result = parse_dimacs(reader);
        assert!(result.is_ok(), "Parsing should succeed");
        let cnf: TestCnf = result.unwrap();

        assert_eq!(cnf.clauses.len(), 0, "Should parse 0 clauses");
    }

    #[test]
    fn test_parse_dimacs_malformed_literal() {
        let dimacs_content = "1 abc 0\n";
        let reader = Cursor::new(dimacs_content);
        let result: Result<Cnf<DoubleLiteral, Vec<DoubleLiteral>>, String> = parse_dimacs(reader);
        assert!(
            result.is_err(),
            "Parsing should fail due to malformed literal"
        );
    }

    #[test]
    fn test_parse_dimacs_no_clauses() {
        let dimacs_content = "p cnf 0 0\n";
        let reader = Cursor::new(dimacs_content);
        let result = parse_dimacs(reader);
        assert!(
            result.is_ok(),
            "Parsing should succeed even with no clauses"
        );
        let cnf: TestCnf = result.unwrap();
        assert!(cnf.clauses.is_empty());
        assert_eq!(cnf.num_vars, 1);
    }
}
