// sat_solver_macros/src/lib.rs

extern crate proc_macro;

use heck::ToPascalCase;
use itertools::Itertools;
use proc_macro::TokenStream;
use quote::{ToTokens, format_ident, quote};
use std::collections::HashMap;
use syn::visit_mut::{self, VisitMut};
use syn::{
    Ident,
    Result,
    Token,
    Type,
    TypePath, // Use syn::Result
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    token, // For token::Bracket
};

// --- Helper for substituting placeholder types ---
const TYPE_LITERAL_PLACEHOLDER: &str = "TyLit";
const TYPE_STORAGE_PLACEHOLDER: &str = "TyStore";
const TYPE_ASSIGNMENT_PLACEHOLDER: &str = "TyAssign";

struct TypeSubstituter<'a> {
    substitutions: &'a HashMap<String, &'a Type>,
}

impl<'a> VisitMut for TypeSubstituter<'a> {
    fn visit_type_mut(&mut self, ty: &mut Type) {
        if let Type::Path(TypePath { qself: None, path }) = ty {
            if path.segments.len() == 1 {
                let ident = &path.segments[0].ident;
                if let Some(replacement) = self.substitutions.get(&ident.to_string()) {
                    *ty = (*replacement).clone();
                    return; // Don't visit further down this replaced path
                }
            }
        }
        // Visit children
        visit_mut::visit_type_mut(self, ty);
    }
}

fn substitute_type(template_ty: &Type, substitutions: &HashMap<String, &Type>) -> Type {
    let mut new_ty = template_ty.clone();
    let mut substituter = TypeSubstituter { substitutions };
    substituter.visit_type_mut(&mut new_ty);
    new_ty
}

// --- Input Parsing Structures ---

struct ComponentInput {
    name: Ident,
    _colon: Token![:],
    _bracket_token: token::Bracket, // Stores the parsed bracket tokens themselves
    types: Punctuated<Type, Token![,]>,
}

impl Parse for ComponentInput {
    fn parse(input: ParseStream) -> Result<Self> {
        // syn::Result
        let component_name: Ident = input.parse()?;
        let colon_token: Token![:] = input.parse()?;

        // Correctly parse bracketed content
        let content_in_brackets;
        let bracket_token = syn::bracketed!(content_in_brackets in input);
        let component_types = Punctuated::parse_terminated(&content_in_brackets)?;

        Ok(Self {
            name: component_name,
            _colon: colon_token,
            _bracket_token: bracket_token,
            types: component_types,
        })
    }
}

struct AllSolverEnumInput {
    enum_name_kw: Ident,
    _eq1: Token![=],
    enum_name: Ident,
    _comma1: Token![,],

    config_prefix_kw: Ident,
    _eq2: Token![=],
    config_prefix: Ident,
    _comma2: Token![,],

    literals: ComponentInput,
    _comma_lit: Token![,],
    literal_storages: ComponentInput,
    _comma_store: Token![,],
    assignments: ComponentInput,
    _comma_assign: Token![,],
    variable_selectors: ComponentInput,
    _comma_select: Token![,],
    propagators: ComponentInput,
    _comma_prop: Token![,],
    restarters: ComponentInput,
    _comma_restart: Token![,],
    clause_managers: ComponentInput,
    _comma_cm: Option<Token![,]>, // Optional comma for the last item
}

impl Parse for AllSolverEnumInput {
    fn parse(input: ParseStream) -> Result<Self> {
        // syn::Result
        Ok(Self {
            enum_name_kw: input.parse()?,
            _eq1: input.parse()?,
            enum_name: input.parse()?,
            _comma1: input.parse()?,
            config_prefix_kw: input.parse()?,
            _eq2: input.parse()?,
            config_prefix: input.parse()?,
            _comma2: input.parse()?,
            literals: input.parse()?,
            _comma_lit: input.parse()?,
            literal_storages: input.parse()?,
            _comma_store: input.parse()?,
            assignments: input.parse()?,
            _comma_assign: input.parse()?,
            variable_selectors: input.parse()?,
            _comma_select: input.parse()?,
            propagators: input.parse()?,
            _comma_prop: input.parse()?,
            restarters: input.parse()?,
            _comma_restart: input.parse()?,
            clause_managers: input.parse()?,
            _comma_cm: input.parse().ok(), // Use .ok() for optional trailing comma
        })
    }
}

fn type_to_string_for_ident(ty: &Type) -> String {
    let type_str = ty.to_token_stream().to_string();
    // Basic sanitization: remove spaces, colons, brackets, etc. Keep generics for uniqueness.
    // Convert to PascalCase to make it a valid Rust identifier part.
    type_str
        .chars()
        .filter(|c| c.is_alphanumeric() || *c == '<' || *c == '>' || *c == '_' || *c == ':')
        .collect::<String>()
        .replace("::", "_") // Replace :: with _
        .replace("<", "Lt") // Replace < with Lt (LessThan)
        .replace(">", "Gt") // Replace > with Gt (GreaterThan)
        .replace("[", "ArrOpen")
        .replace("]", "ArrClose")
        .replace(" ", "")
        .replace(",", "Comma")
        .to_pascal_case()
}

#[proc_macro]
pub fn all_solver_enum(input: TokenStream) -> TokenStream {
    let parsed_input = parse_macro_input!(input as AllSolverEnumInput);

    let enum_name = parsed_input.enum_name;
    let config_prefix = parsed_input.config_prefix;

    let literals_list: Vec<_> = parsed_input.literals.types.iter().collect();
    let literal_storages_list: Vec<_> = parsed_input.literal_storages.types.iter().collect();
    let assignments_list: Vec<_> = parsed_input.assignments.types.iter().collect();
    let variable_selectors_list: Vec<_> = parsed_input.variable_selectors.types.iter().collect();
    let propagators_list: Vec<_> = parsed_input.propagators.types.iter().collect();
    let restarters_list: Vec<_> = parsed_input.restarters.types.iter().collect();
    let clause_managers_list: Vec<_> = parsed_input.clause_managers.types.iter().collect();

    let mut generated_configs = Vec::new();
    let mut enum_variants = Vec::new();
    let mut from_str_match_arms = Vec::new();

    // Cartesian product of all component types
    for (
        lit_ty,
        store_template_ty,
        assign_ty,
        sel_ty,
        prop_template_ty,
        restart_ty,
        cm_template_ty,
    ) in itertools::iproduct!(
        literals_list.iter(),
        literal_storages_list.iter(),
        assignments_list.iter(),
        variable_selectors_list.iter(),
        propagators_list.iter(),
        restarters_list.iter(),
        clause_managers_list.iter()
    ) {
        let mut current_substitutions = HashMap::new();
        current_substitutions.insert(TYPE_LITERAL_PLACEHOLDER.to_string(), *lit_ty);
        current_substitutions.insert(TYPE_ASSIGNMENT_PLACEHOLDER.to_string(), *assign_ty);
        // Note: TyStore depends on TyLit, so substitute it first
        let store_ty = substitute_type(store_template_ty, &current_substitutions);
        current_substitutions.insert(TYPE_STORAGE_PLACEHOLDER.to_string(), &store_ty);

        let final_prop_ty = substitute_type(prop_template_ty, &current_substitutions);
        let final_cm_ty = substitute_type(cm_template_ty, &current_substitutions);

        let config_name_str = format!(
            "{}_{}_{}_{}_{}_{}_{}_{}",
            config_prefix,
            type_to_string_for_ident(lit_ty),
            type_to_string_for_ident(&store_ty),
            type_to_string_for_ident(assign_ty),
            type_to_string_for_ident(sel_ty),
            type_to_string_for_ident(&final_prop_ty),
            type_to_string_for_ident(restart_ty),
            type_to_string_for_ident(&final_cm_ty)
        );

        let config_ident = format_ident!("{}", config_name_str);

        generated_configs.push(quote! {
            crate::sat::solver::solver_config!(
                #config_ident {
                    Literal = #lit_ty,
                    LiteralStorage = #store_ty,
                    Assignment = #assign_ty,
                    VariableSelector = #sel_ty,
                    Propagator = #final_prop_ty,
                    Restarter = #restart_ty,
                    ClauseManager = #final_cm_ty,
                }
            );
        });

        enum_variants.push(quote! {
            #config_ident(#config_ident)
        });

        from_str_match_arms.push(quote! {
            stringify!(#config_ident) => {
                Ok(#enum_name::#config_ident(#config_ident::default()))
            }
        })
    }

    let output = quote! {
        #(#generated_configs)*

        /// Enum holding all generated solver configurations.
        #[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub enum #enum_name {
            #(#enum_variants),*
        }
    };

    output.into()
}
