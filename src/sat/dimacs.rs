// a parser for the DIMACS format

use std::io::{self, BufRead};
use std::str::FromStr;

use crate::sat::cnf::Cnf;
use crate::sat::clause::Clause;
use crate::sat::literal::Literal;

pub fn parse_dimacs<R: BufRead>(reader: R) -> Cnf {
    let mut lines = reader.lines().map(|l| l.unwrap());

    let mut clauses = Vec::new();

    for line in &mut lines {
        let mut parts = line.split_whitespace();

        match parts.clone().peekable().peek() {
            Some(&"p" | &"c") => continue,
            Some(&"%") | None => break,
            Some(_) => {
                let clause = parts.map(|s| s.parse().unwrap()).filter(|p| *p != 0).collect();
                clauses.push(clause);
            }
        }
    }
    
    Cnf::new(clauses)
}

pub fn parse_file(file: &str) -> io::Result<Cnf> {
    let file = std::fs::File::open(file)?;
    let reader = io::BufReader::new(file);
    Ok(parse_dimacs(reader))
}