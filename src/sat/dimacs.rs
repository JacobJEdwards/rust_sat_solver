// a parser for the DIMACS format

use std::io::{self, BufRead};

use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;


// panics docs

/// Parses a DIMACS file into a CNF.
/// # Panics
/// if the file is not in DIMACS format.
pub fn parse_dimacs<R: BufRead, L: Literal>(reader: R) -> Cnf<L> {
    let mut lines = reader.lines().map(|l| l.unwrap());

    let mut clauses = Vec::new();

    for line in &mut lines {
        let parts = line.split_whitespace();

        match parts.clone().peekable().peek() {
            Some(&"p" | &"c") => continue,
            Some(&"%") | None => break,
            Some(_) => {
                let clause = parts
                    .map(|s| s.parse().unwrap())
                    .filter(|p| *p != 0)
                    .collect();
                clauses.push(clause);
            }
        }
    }

    Cnf::new(clauses)
}

/// Parses a DIMACS file into a CNF.
/// # Errors
/// if the file cannot be read.
pub fn parse_file<T: Literal>(file: &str) -> io::Result<Cnf<T>> {
    let file = std::fs::File::open(file)?;
    let reader = io::BufReader::new(file);
    Ok(parse_dimacs(reader))
}

pub fn get_all_files(dir: &str) -> io::Result<Vec<String>> {
    let mut files = Vec::new();

    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();

        if path.is_file() {
            let path = path.to_str().unwrap().to_string();
            files.push(path);
        } else {
            let mut sub_files = get_all_files(path.to_str().unwrap())?;
            files.append(&mut sub_files);
        }
    }

    Ok(files)
}
