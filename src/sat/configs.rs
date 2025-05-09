use crate::sat::assignment::{HashMapAssignment, VecAssignment};
use crate::sat::clause_management::{LbdClauseManagement, NoClauseManagement};
use crate::sat::literal::{DoubleLiteral, NegativeLiteral, PackedLiteral, StructLiteral};
use crate::sat::propagation::{UnitPropagationWithPureLiterals, UnitSearch, WatchedLiterals};
use crate::sat::restarter::{Geometric, Linear, Luby, Never};
use crate::sat::solver::SolverConfig;
use crate::sat::variable_selection::{
    FixedOrder, JeroslowWangOneSided, JeroslowWangTwoSided, RandomOrder, Vsids, VsidsHeap,
};
use smallvec::SmallVec;
use std::fmt::Debug;

use sat_solver_macros::all_solver_enum;

all_solver_enum! {
    enum_name = AllSolverConfigs,
    config_prefix = SpecificSolverConfig,
    literals: [
        PackedLiteral,
        NegativeLiteral,
        StructLiteral,
        DoubleLiteral,
    ],
    literal_storages: [
        SmallVec<[TyLit; 8]>,
        Vec<TyLit>,
        SmallVec<[TyLit; 16]>,
    ],
    assignments: [
        VecAssignment,
        HashMapAssignment,
    ],
    variable_selectors: [
        Vsids,
        JeroslowWangOneSided,
        JeroslowWangTwoSided,
        VsidsHeap,
        FixedOrder,
        RandomOrder,
    ],
    propagators: [
        WatchedLiterals<TyLit, TyStore, TyAssign>,
        UnitSearch<TyLit, TyStore, TyAssign>,
        UnitPropagationWithPureLiterals<TyLit, TyStore, TyAssign>,
    ],
    restarters: [
        Luby<2>,
        Never,
        Linear<100>,
        Geometric<2>,
    ],
    clause_managers: [
        LbdClauseManagement<TyLit, TyStore, 10>,
        NoClauseManagement<TyLit, TyStore>,
    ],
}
