#![allow(non_camel_case_types)]

mod enums;
mod generated;

use cxx;
use cxx::{type_id, ExternType};

pub use enums::{AstKind, AstPrintMode, DeclKind, ErrorCode, GoalPrec, ParamKind, ParameterKind, SortKind, SymbolKind, Z3_lbool};

pub type Z3_error_handler =
    ::std::option::Option<unsafe extern "C" fn(c: *mut ffi::_Z3_context, e: ErrorCode)>;
extern "C" {
    pub fn Z3_set_error_handler(c: *mut ffi::_Z3_context, h: Z3_error_handler);
}

unsafe impl ExternType for AstKind {
    type Id = type_id!("Z3_ast_kind");
    type Kind = cxx::kind::Trivial;
}

unsafe impl ExternType for AstPrintMode {
    type Id = type_id!("Z3_ast_print_mode");
    type Kind = cxx::kind::Trivial;
}

unsafe impl ExternType for DeclKind {
    type Id = type_id!("Z3_decl_kind");
    type Kind = cxx::kind::Trivial;
}

unsafe impl ExternType for ErrorCode {
    type Id = type_id!("Z3_error_code");
    type Kind = cxx::kind::Trivial;
}

unsafe impl ExternType for GoalPrec {
    type Id = type_id!("Z3_goal_prec");
    type Kind = cxx::kind::Trivial;
}

unsafe impl ExternType for ParamKind {
    type Id = type_id!("Z3_param_kind");
    type Kind = cxx::kind::Trivial;
}

unsafe impl ExternType for ParameterKind {
    type Id = type_id!("Z3_parameter_kind");
    type Kind = cxx::kind::Trivial;
}

unsafe impl ExternType for SortKind {
    type Id = type_id!("Z3_sort_kind");
    type Kind = cxx::kind::Trivial;
}

unsafe impl ExternType for SymbolKind {
    type Id = type_id!("Z3_symbol_kind");
    type Kind = cxx::kind::Trivial;
}

unsafe impl ExternType for Z3_lbool {
    type Id = type_id!("Z3_lbool");
    type Kind = cxx::kind::Trivial;
}

pub type Z3_bool = bool;
pub const Z3_TRUE: Z3_bool = true;
pub const Z3_FALSE: Z3_bool = false;

#[cxx::bridge]
pub mod ffi {
    unsafe extern "C++" {
        include!("z3_cxx/include/z3_inc.h");

        type Z3_error_handler;

        type _Z3_config;
        type _Z3_context;
        type _Z3_sort;
        type _Z3_ast;
        type _Z3_model;
        type _Z3_string;
        type _Z3_func_decl;
        type _Z3_symbol;
        type _Z3_literal;
        type _Z3_app;
        type _Z3_pattern;
        type _Z3_constructor;
        type _Z3_constructor_list;
        type _Z3_params;
        type _Z3_param_descrs;
        type _Z3_goal;
        type _Z3_tactic;
        type _Z3_probe;
        type _Z3_stats;
        type _Z3_solver;
        type _Z3_solver_callback;
        type _Z3_ast_vector;
        type _Z3_ast_map;
        type _Z3_apply_result;
        type _Z3_func_interp;
        type _Z3_func_entry;
        type _Z3_fixedpoint;
        type _Z3_optimize;
        type _Z3_rcf_num;

        type Z3_string;
        type Z3_char_ptr;
        type Z3_string_ptr;

        type Z3_ast_kind = crate::AstKind;
        type Z3_lbool = crate::Z3_lbool;
        type Z3_parameter_kind = crate::ParameterKind;
        type Z3_symbol_kind = crate::SymbolKind;
        type Z3_sort_kind = crate::SortKind;
        type Z3_error_code = crate::ErrorCode;
        type Z3_ast_print_mode = crate::AstPrintMode;
        type Z3_param_kind = crate::ParamKind;
        type Z3_decl_kind = crate::DeclKind;
        type Z3_goal_prec = crate::GoalPrec;

        pub fn Z3_mk_config() -> *mut _Z3_config;
        pub fn Z3_global_param_reset_all();
    }

    extern "C++" {
        include!("z3_cxx/include/z3_inc.h");

        pub unsafe fn Z3_global_param_set(param_id: *mut _Z3_string, param_value: *mut _Z3_string);
        pub unsafe fn Z3_global_param_get(param_id: *mut _Z3_string, param_value: *mut Z3_char_ptr) -> bool;

        pub unsafe fn Z3_del_config(c: *mut _Z3_config);
        pub unsafe fn Z3_set_param_value(c: *mut _Z3_config, param_id: *const c_char, param_value: *const c_char);

        pub unsafe fn Z3_mk_context(c: *mut _Z3_config) -> *mut _Z3_context;
        pub unsafe fn Z3_mk_context_rc(c: *mut _Z3_config) -> *mut _Z3_context;
        pub unsafe fn Z3_del_context(c: *mut _Z3_context);
        pub unsafe fn Z3_inc_ref(c: *mut _Z3_context, a: *mut _Z3_ast);
        pub unsafe fn Z3_dec_ref(c: *mut _Z3_context, a: *mut _Z3_ast);

        pub unsafe fn Z3_update_param_value(c: *mut _Z3_context, param_id: *mut _Z3_string, param_value: *mut _Z3_string);
        pub unsafe fn Z3_interrupt(c: *mut _Z3_context);

        pub unsafe fn Z3_mk_params(c: *mut _Z3_context) -> *mut _Z3_params;
        pub unsafe fn Z3_params_inc_ref(c: *mut _Z3_context, p: *mut _Z3_params);
        pub unsafe fn Z3_params_dec_ref(c: *mut _Z3_context, p: *mut _Z3_params);
        pub unsafe fn Z3_params_set_bool(c: *mut _Z3_context, p: *mut _Z3_params, k: *mut _Z3_symbol, v: bool);
        pub unsafe fn Z3_params_set_uint(c: *mut _Z3_context, p: *mut _Z3_params, k: *mut _Z3_symbol, v: u32);
        pub unsafe fn Z3_params_set_double(c: *mut _Z3_context, p: *mut _Z3_params, k: *mut _Z3_symbol, v: f64);
        pub unsafe fn Z3_params_set_symbol(c: *mut _Z3_context, p: *mut _Z3_params, k: *mut _Z3_symbol, v: *mut _Z3_symbol);
        pub unsafe fn Z3_params_to_string(c: *mut _Z3_context, p: *mut _Z3_params) -> *const c_char;
        pub unsafe fn Z3_tactic_apply_ex(c: *mut _Z3_context, t: *mut _Z3_tactic, g: *mut _Z3_goal, p: *mut _Z3_params) -> *mut _Z3_apply_result;
        pub unsafe fn Z3_tactic_apply(c: *mut _Z3_context, t: *mut _Z3_tactic, g: *mut _Z3_goal) -> *mut _Z3_apply_result;
        pub unsafe fn Z3_tactic_fail_if(c: *mut _Z3_context, p: *mut _Z3_probe) -> *mut _Z3_tactic;
        pub unsafe fn Z3_tactic_cond(c: *mut _Z3_context, p: *mut _Z3_probe, t1: *mut _Z3_tactic, t2: *mut _Z3_tactic) -> *mut _Z3_tactic;
        pub unsafe fn Z3_tactic_when(c: *mut _Z3_context, p: *mut _Z3_probe, t: *mut _Z3_tactic) -> *mut _Z3_tactic;
        pub unsafe fn Z3_tactic_or_else(c: *mut _Z3_context, t1: *mut _Z3_tactic, t2: *mut _Z3_tactic) -> *mut _Z3_tactic;
        pub unsafe fn Z3_tactic_and_then(c: *mut _Z3_context, t1: *mut _Z3_tactic, t2: *mut _Z3_tactic) -> *mut _Z3_tactic;
        pub unsafe fn Z3_tactic_repeat(c: *mut _Z3_context, t: *mut _Z3_tactic, max: u32) -> *mut _Z3_tactic;
        pub unsafe fn Z3_tactic_fail(c: *mut _Z3_context) -> *mut _Z3_tactic;
        pub unsafe fn Z3_tactic_skip(c: *mut _Z3_context) -> *mut _Z3_tactic;
        pub unsafe fn Z3_get_tactic_name(c: *mut _Z3_context, i: u32) -> *const c_char;

        pub unsafe fn Z3_get_probe_name(c: *mut _Z3_context, i: u32) -> *const c_char;
        pub unsafe fn Z3_probe_dec_ref(c: *mut _Z3_context, p: *mut _Z3_probe);
        pub unsafe fn Z3_probe_inc_ref(c: *mut _Z3_context, p: *mut _Z3_probe);
        pub unsafe fn Z3_probe_not(x: *mut _Z3_context, p: *mut _Z3_probe) -> *mut _Z3_probe;
        pub unsafe fn Z3_probe_eq(x: *mut _Z3_context, p1: *mut _Z3_probe, p2: *mut _Z3_probe) -> *mut _Z3_probe;
        pub unsafe fn Z3_probe_or(x: *mut _Z3_context, p1: *mut _Z3_probe, p2: *mut _Z3_probe) -> *mut _Z3_probe;
        pub unsafe fn Z3_probe_and(x: *mut _Z3_context, p1: *mut _Z3_probe, p2: *mut _Z3_probe) -> *mut _Z3_probe;
        pub unsafe fn Z3_probe_ge(x: *mut _Z3_context, p1: *mut _Z3_probe, p2: *mut _Z3_probe) -> *mut _Z3_probe;
        pub unsafe fn Z3_probe_le(x: *mut _Z3_context, p1: *mut _Z3_probe, p2: *mut _Z3_probe) -> *mut _Z3_probe;
        pub unsafe fn Z3_probe_gt(x: *mut _Z3_context, p1: *mut _Z3_probe, p2: *mut _Z3_probe) -> *mut _Z3_probe;
        pub unsafe fn Z3_probe_lt(x: *mut _Z3_context, p1: *mut _Z3_probe, p2: *mut _Z3_probe) -> *mut _Z3_probe;
        pub unsafe fn Z3_probe_const(x: *mut _Z3_context, val: f64) -> *mut _Z3_probe;
        pub unsafe fn Z3_probe_apply(c: *mut _Z3_context, p: *mut _Z3_probe, g: *mut _Z3_goal) -> f64;
        pub unsafe fn Z3_mk_probe(c: *mut _Z3_context, name: *const c_char) -> *mut _Z3_probe;
        pub unsafe fn Z3_probe_get_descr(c: *mut _Z3_context, name: *const c_char) -> *const c_char;
        pub unsafe fn Z3_get_num_probes(c: *mut _Z3_context) -> u32;




        pub unsafe fn Z3_get_num_tactics(c: *mut _Z3_context) -> u32;
        pub unsafe fn Z3_goal_inc_ref(c: *mut _Z3_context, g: *mut _Z3_goal);
        pub unsafe fn Z3_goal_dec_ref(c: *mut _Z3_context, g: *mut _Z3_goal);
        pub unsafe fn Z3_apply_result_get_subgoal(c: *mut _Z3_context, r: *mut _Z3_apply_result, i: u32) -> *mut _Z3_goal;
        pub unsafe fn Z3_apply_result_get_num_subgoals(c: *mut _Z3_context, r: *mut _Z3_apply_result) -> u32;
        pub unsafe fn Z3_goal_to_string(c: *mut _Z3_context, g: *mut _Z3_goal) -> *const c_char;
        pub unsafe fn Z3_goal_formula(c: *mut _Z3_context, g: *mut _Z3_goal, idx: u32) -> *mut _Z3_ast;
        pub unsafe fn Z3_goal_precision(c: *mut _Z3_context, g: *mut _Z3_goal) -> Z3_goal_prec;
        pub unsafe fn Z3_goal_translate(source: *mut _Z3_context, g: *mut _Z3_goal, target: *mut _Z3_context) -> *mut _Z3_goal;
        pub unsafe fn Z3_goal_reset(c: *mut _Z3_context, g: *mut _Z3_goal);
        pub unsafe fn Z3_goal_is_decided_sat(c: *mut _Z3_context, g: *mut _Z3_goal) -> bool;
        pub unsafe fn Z3_goal_is_decided_unsat(c: *mut _Z3_context, g: *mut _Z3_goal) -> bool;
        pub unsafe fn Z3_mk_goal(c: *mut _Z3_context, models: bool, unsat_cores: bool, proofs: bool) -> *mut _Z3_goal;
        pub unsafe fn Z3_goal_assert(c: *mut _Z3_context, g: *mut _Z3_goal, a: *mut _Z3_ast);
        pub unsafe fn Z3_goal_inconsistent(c: *mut _Z3_context, g: *mut _Z3_goal) -> bool;
        pub unsafe fn Z3_goal_depth(c: *mut _Z3_context, g: *mut _Z3_goal) -> u32;
        pub unsafe fn Z3_goal_size(c: *mut _Z3_context, g: *mut _Z3_goal) -> u32;
        pub unsafe fn Z3_goal_num_exprs(c: *mut _Z3_context, g: *mut _Z3_goal) -> u32;

        pub unsafe fn Z3_mk_constructor_list(c: *mut _Z3_context,
            num_constructors: u32,
            constructors: *const *mut _Z3_constructor
        ) -> *mut _Z3_constructor_list;

        pub unsafe fn Z3_del_constructor_list(c: *mut _Z3_context, clist: *mut _Z3_constructor_list);
        pub unsafe fn Z3_del_constructor(c: *mut _Z3_context, constr: *mut _Z3_constructor);
        pub unsafe fn Z3_get_datatype_sort_constructor_accessor(c: *mut _Z3_context,
            t: *mut _Z3_sort,
            _Z3_func_decl: u32,
            idx_a: u32) -> *mut _Z3_func_decl;
        pub unsafe fn Z3_get_datatype_sort_recognizer(
            c: *mut _Z3_context, t: *mut _Z3_sort, idx: u32
        ) -> *mut _Z3_func_decl;
        pub unsafe fn Z3_get_datatype_sort_constructor(
            c: *mut _Z3_context, t: *mut _Z3_sort, idx: u32
        ) -> *mut _Z3_func_decl;
        pub unsafe fn Z3_mk_constructor(c: *mut _Z3_context,
            name: *mut _Z3_symbol,
            recognizer: *mut _Z3_symbol,
            num_fields: u32,
            field_names: *const *mut _Z3_symbol,
            sorts: *const *mut _Z3_sort,
            sort_refs: *mut u32,
        ) -> *mut _Z3_constructor;
        pub unsafe fn Z3_mk_datatypes(c: *mut _Z3_context,
            num_sorts: u32,
            sort_names: *const *mut _Z3_symbol,
            sorts: *mut *mut _Z3_sort,
            constructor_lists: *mut *mut _Z3_constructor_list);





        pub unsafe fn Z3_mk_string_symbol(
            c: *mut _Z3_context,
            s: *const c_char,
        ) -> *mut _Z3_symbol;
        pub unsafe fn Z3_sort_to_ast(c: *mut _Z3_context, s: *mut _Z3_sort) -> *mut _Z3_ast;
        pub unsafe fn Z3_is_eq_sort(c: *mut _Z3_context, s1: *mut _Z3_sort, s2: *mut _Z3_sort) -> bool;
        pub unsafe fn Z3_sort_to_string(c: *mut _Z3_context, s: *mut _Z3_sort) -> *const c_char;
        pub unsafe fn Z3_get_array_sort_range(c: *mut _Z3_context, s: *mut _Z3_sort) -> *mut _Z3_sort;
        pub unsafe fn Z3_get_array_sort_domain(c: *mut _Z3_context, t: *mut _Z3_sort) -> *mut _Z3_sort;

        pub unsafe fn Z3_mk_const(
            c: *mut _Z3_context,
            s: *mut _Z3_symbol,
            ty: *mut _Z3_sort,
        ) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_fresh_const(
            c: *mut _Z3_context,
            prefix: *const c_char,
            ty: *mut _Z3_sort,
        ) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_exists_const(
            c: *mut _Z3_context,
            weight: u32,
            num_bound: u32,
            bound: *const *mut _Z3_app,
            num_patterns: u32,
            patterns: *const *mut _Z3_pattern,
            body: *mut _Z3_ast,
        ) -> *mut _Z3_ast;

        pub unsafe fn Z3_mk_true(c: *mut _Z3_context) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_false(c: *mut _Z3_context) -> *mut _Z3_ast;
        pub unsafe fn Z3_get_bool_value(c: *mut _Z3_context, a: *mut _Z3_ast) -> Z3_lbool;
        pub unsafe fn Z3_translate(source: *mut _Z3_context, a: *mut _Z3_ast, target: *mut _Z3_context) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_ite(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast, t3: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_not(c: *mut _Z3_context, a: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_real(c: *mut _Z3_context, num: i32, den: i32) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_distinct(c: *mut _Z3_context, num_args: u32, args: *const *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_add(c: *mut _Z3_context, num_args: u32, args: *const *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_sub(c: *mut _Z3_context, num_args: u32, args: *const *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_mul(c: *mut _Z3_context, num_args: u32, args: *const *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_power(c: *mut _Z3_context, arg1: *mut _Z3_ast, arg2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_and(c: *mut _Z3_context, num_args: u32, args: *const *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_or(c: *mut _Z3_context, num_args: u32, args: *const *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_xor(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;

        pub unsafe fn Z3_mk_eq(c: *mut _Z3_context, l: *mut _Z3_ast, r: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_lt(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_le(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_gt(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_ge(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_divides(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_simplify(c: *mut _Z3_context, a: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_substitute(c: *mut _Z3_context,
            a: *mut _Z3_ast,
            num_exprs: u32,
            from: *const *mut _Z3_ast,
            to: *const *mut _Z3_ast) -> *mut _Z3_ast;

        pub unsafe fn Z3_to_app(c: *mut _Z3_context, a: *mut _Z3_ast) -> *mut _Z3_app;
        pub unsafe fn Z3_get_app_num_args(c: *mut _Z3_context, a: *mut _Z3_app) -> u32;
        pub unsafe fn Z3_get_app_arg(c: *mut _Z3_context, a: *mut _Z3_app, i: u32) -> *mut _Z3_ast;

        pub unsafe fn Z3_mk_implies(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_unary_minus(c: *mut _Z3_context, args: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_div(c: *mut _Z3_context, arg1: *mut _Z3_ast, arg2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_iff(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_int2real(c: *mut _Z3_context, t1: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_pble(c: *mut _Z3_context, num_args: u32,
            args: *const *mut _Z3_ast, coeffs: *const i32,
            k: i32) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_pbge(c: *mut _Z3_context, num_args: u32,
            args: *const *mut _Z3_ast, coeffs: *const i32,
            k: i32) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_pbeq(c: *mut _Z3_context, num_args: u32,
            args: *const *mut _Z3_ast, coeffs: *const i32,
            k: i32) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_int64(c: *mut _Z3_context, v: i64, ty: *mut _Z3_sort) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_unsigned_int64(c: *mut _Z3_context, v: u64, ty: *mut _Z3_sort) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_is_int(c: *mut _Z3_context, t1: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_int_symbol(c: *mut _Z3_context, i: i32) -> *mut _Z3_symbol;

        pub unsafe fn Z3_mk_numeral(c: *mut _Z3_context, numeral: *const c_char, ty: *mut _Z3_sort) -> *mut _Z3_ast;

        pub unsafe fn Z3_mk_simple_solver(c: *mut _Z3_context) -> *mut _Z3_solver;
        pub unsafe fn Z3_solver_assert(
            c: *mut _Z3_context, s: *mut _Z3_solver, a: *mut _Z3_ast);
        pub unsafe fn Z3_solver_check(c: *mut _Z3_context, s: *mut _Z3_solver) -> Z3_lbool;
        pub unsafe fn Z3_solver_dec_ref(c: *mut _Z3_context, s: *mut _Z3_solver);
        pub unsafe fn Z3_solver_inc_ref(c: *mut _Z3_context, s: *mut _Z3_solver);
        pub unsafe fn Z3_solver_to_string(c: *mut _Z3_context, s: *mut _Z3_solver) -> *const c_char;
        pub unsafe fn Z3_solver_set_params(c: *mut _Z3_context, s: *mut _Z3_solver, p: *mut _Z3_params);
        pub unsafe fn Z3_solver_get_reason_unknown(c: *mut _Z3_context, s: *mut _Z3_solver) -> *const c_char;
        pub unsafe fn Z3_solver_get_proof(c: *mut _Z3_context, s: *mut _Z3_solver) -> *mut _Z3_ast;
        pub unsafe fn Z3_solver_pop(c: *mut _Z3_context, s: *mut _Z3_solver, n: u32);
        pub unsafe fn Z3_solver_push(c: *mut _Z3_context, s: *mut _Z3_solver);
        pub unsafe fn Z3_solver_get_unsat_core(c: *mut _Z3_context, s: *mut _Z3_solver) -> *mut _Z3_ast_vector;
        pub unsafe fn Z3_solver_check_assumptions(c: *mut _Z3_context, s: *mut _Z3_solver,
            num_assumptions: u32, assumptions: *const * mut _Z3_ast) -> Z3_lbool;
        pub unsafe fn Z3_solver_reset(c: *mut _Z3_context, s: *mut _Z3_solver);
        pub unsafe fn Z3_solver_assert_and_track(c: *mut _Z3_context, s: *mut _Z3_solver, a: *mut _Z3_ast, p: *mut _Z3_ast);
        pub unsafe fn Z3_solver_translate(source: *mut _Z3_context, s: *mut _Z3_solver, target: *mut _Z3_context) -> *mut _Z3_solver;
        pub unsafe fn Z3_mk_solver(c: *mut _Z3_context) -> *mut _Z3_solver;
        pub unsafe fn Z3_pattern_to_string(c: *mut _Z3_context, p: *mut _Z3_pattern) -> *const c_char;
        pub unsafe fn Z3_mk_pattern(c: *mut _Z3_context, num_patterns: u32, terms: *const *mut _Z3_ast) -> *mut _Z3_pattern;




        pub unsafe fn Z3_solver_get_model(c: *mut _Z3_context, s: *mut _Z3_solver) -> *mut _Z3_model;
        pub unsafe fn Z3_model_to_string(c: *mut _Z3_context, m: *mut _Z3_model) -> *mut c_char;
        pub unsafe fn Z3_ast_to_string(c: *mut _Z3_context, a: *mut _Z3_ast) -> *mut c_char;
        pub unsafe fn Z3_is_eq_ast(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> bool;
        pub unsafe fn Z3_get_ast_hash(c: *mut _Z3_context, a: *mut _Z3_ast) -> u32;
        pub unsafe fn Z3_get_ast_id(c: *mut _Z3_context, t: *mut _Z3_ast) -> u32;

        pub unsafe fn Z3_get_ast_kind(c: *mut _Z3_context, a: *mut _Z3_ast) -> Z3_ast_kind;

        pub unsafe fn Z3_model_eval(
            c: *mut _Z3_context,
            m: *mut _Z3_model,
            t: *mut _Z3_ast,
            model_completion: bool,
            v :*mut *mut _Z3_ast,
        ) -> bool;

        pub unsafe fn Z3_get_numeral_int(c: *mut _Z3_context, v: *mut _Z3_ast, i: *mut i32) -> bool;
        pub unsafe fn Z3_get_symbol_int(c: *mut _Z3_context, s: *mut _Z3_symbol) -> i32;
        pub unsafe fn Z3_get_symbol_string(c: *mut _Z3_context, s: *mut _Z3_symbol) -> *const c_char;
        pub unsafe fn Z3_get_symbol_kind(c: *mut _Z3_context, s: *mut _Z3_symbol) -> Z3_symbol_kind;
        pub unsafe fn Z3_get_decl_name(c: *mut _Z3_context, d: *mut _Z3_func_decl) -> *mut _Z3_symbol;
        pub unsafe fn Z3_get_decl_kind(c: *mut _Z3_context, d: *mut _Z3_func_decl) -> Z3_decl_kind;
        pub unsafe fn Z3_mk_app(
            c: *mut _Z3_context,
            d: *mut _Z3_func_decl,
            num_args: u32,
            args: *const *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_get_arity(c: *mut _Z3_context, d: *mut _Z3_func_decl) -> u32;

        pub unsafe fn Z3_get_numeral_small(c: *mut _Z3_context, v: *mut _Z3_ast, num: *mut i64, den: *mut i64) -> bool;
        pub unsafe fn Z3_mk_mod(c: *mut _Z3_context, arg1: *mut _Z3_ast, arg2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_rem(c: *mut _Z3_context, arg1: *mut _Z3_ast, arg2: *mut _Z3_ast) -> *mut _Z3_ast;

        pub unsafe fn Z3_mk_func_decl(c: *mut _Z3_context, s: *mut _Z3_symbol,
            domain_size: u32, domain: *const *mut _Z3_sort, range: *mut _Z3_sort) -> *mut _Z3_func_decl;

        pub unsafe fn Z3_get_sort(c: *mut _Z3_context, a: *mut _Z3_ast) -> *mut _Z3_sort;
        pub unsafe fn Z3_is_string_sort(c: *mut _Z3_context, s: *mut _Z3_sort) -> bool;

        pub unsafe fn Z3_mk_forall_const(
            c: *mut _Z3_context,
            weight: u32,
            num_bound: u32,
            bound: *const *mut _Z3_app,
            num_patterns: u32,
            patterns: *const *mut _Z3_pattern,
            body: *mut _Z3_ast
        ) -> *mut _Z3_ast;
        pub unsafe fn Z3_get_sort_kind(c: *mut _Z3_context, t: *mut _Z3_sort) -> Z3_sort_kind;
        pub unsafe fn Z3_mk_enumeration_sort(c: *mut _Z3_context,
            name: *mut _Z3_symbol,
            n: u32,
            enum_names: *const *mut _Z3_symbol,
            enum_consts: *mut *mut _Z3_func_decl,
            enum_testers: *mut *mut _Z3_func_decl) -> *mut _Z3_sort;

        pub unsafe fn Z3_mk_bool_sort(c: *mut _Z3_context) -> *mut _Z3_sort;
        pub unsafe fn Z3_mk_int_sort(c: *mut _Z3_context) -> *mut _Z3_sort;
        pub unsafe fn Z3_mk_real_sort(c: *mut _Z3_context) -> *mut _Z3_sort;
        pub unsafe fn Z3_mk_string_sort(c: *mut _Z3_context) -> *mut _Z3_sort;

        pub unsafe fn Z3_mk_set_sort(c: *mut _Z3_context, ty: *mut _Z3_sort) -> *mut _Z3_sort;
        pub unsafe fn Z3_mk_array_sort(c: *mut _Z3_context, domain: *mut _Z3_sort, range: *mut _Z3_sort) -> *mut _Z3_sort;
        pub unsafe fn Z3_mk_bv_sort(c: *mut _Z3_context, sz: u32) -> *mut _Z3_sort;
        pub unsafe fn Z3_mk_uninterpreted_sort(c: *mut _Z3_context, s: *mut _Z3_symbol) -> *mut _Z3_sort;

        pub unsafe fn Z3_apply_result_dec_ref(c: *mut _Z3_context, r: *mut _Z3_apply_result);
        pub unsafe fn Z3_apply_result_inc_ref(c: *mut _Z3_context, r: *mut _Z3_apply_result);



        pub unsafe fn Z3_mk_set_difference(c: *mut _Z3_context, arg1: *mut _Z3_ast, arg2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_set_subset(c: *mut _Z3_context, arg1: *mut _Z3_ast, arg2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_set_complement(c: *mut _Z3_context, arg1: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_set_intersect(c: *mut _Z3_context, num_args: u32, args: *const *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_set_union(c: *mut _Z3_context, num_args: u32, args: *const *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_set_member(c: *mut _Z3_context, elem: *mut _Z3_ast, set: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_set_add(c: *mut _Z3_context, set: *mut _Z3_ast, elem: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_const_array(c: *mut _Z3_context, set: *mut _Z3_sort, v: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_store(c: *mut _Z3_context, a: *mut _Z3_ast, i: *mut _Z3_ast, v: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_select(c: *mut _Z3_context, a: *mut _Z3_ast, i: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_zero_ext(c: *mut _Z3_context, i: u32, t1: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_extract(c: *mut _Z3_context, high: u32, low: u32, t1: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_sign_ext(c: *mut _Z3_context, i: u32, t1: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvmul_no_underflow(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvsdiv_no_overflow(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvsub_no_overflow(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvadd_no_underflow(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvmul_no_overflow(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast, is_signed: bool) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvsub_no_underflow(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast, is_signed: bool) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvadd_no_overflow(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast, is_signed: bool) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvneg_no_overflow(c: *mut _Z3_context, t1: *mut _Z3_ast) -> *mut _Z3_ast;

        pub unsafe fn Z3_mk_concat(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_ext_rotate_left(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_ext_rotate_right(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvashr(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvlshr(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvshl(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvsgt(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvugt(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvsge(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvuge(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvsle(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvule(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvslt(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvult(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvsmod(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvsrem(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvurem(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvsdiv(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvudiv(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvmul(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvsub(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvadd(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvxnor(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvnor(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvnand(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvxor(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvor(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvand(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bv2int(c: *mut _Z3_context, t1: *mut _Z3_ast, is_signed: bool) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_real2int(c: *mut _Z3_context, t1: *mut _Z3_ast) -> *mut _Z3_ast;

        pub unsafe fn Z3_mk_bvredor(c: *mut _Z3_context, t1: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvredand(c: *mut _Z3_context, t1: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvneg(c: *mut _Z3_context, t1: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_bvnot(c: *mut _Z3_context, t1: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_int2bv(c: *mut _Z3_context, n: u32, t1: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_get_numeral_uint64(c: *mut _Z3_context, v: *mut _Z3_ast, u: *mut u64) -> bool;
        pub unsafe fn Z3_mk_string(c: *mut _Z3_context, s: *const c_char) -> *mut _Z3_ast;
        pub unsafe fn Z3_get_string(c: *mut _Z3_context, s: *mut _Z3_ast) -> *mut c_char;
        pub unsafe fn Z3_func_decl_to_string(c: *mut _Z3_context, d: *mut _Z3_func_decl) -> *mut c_char;

        pub unsafe fn Z3_get_bv_sort_size(c: *mut _Z3_context, t: *mut _Z3_sort) -> u32;
        pub unsafe fn Z3_get_numeral_int64(c: *mut _Z3_context, v: *mut _Z3_ast, i: *mut i64) -> bool;

        pub unsafe fn Z3_mk_seq_prefix(c: *mut _Z3_context, suffix: *mut _Z3_ast, s: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_seq_suffix(c: *mut _Z3_context, suffix: *mut _Z3_ast, s: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_seq_contains(c: *mut _Z3_context, container: *mut _Z3_ast, containee: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_seq_concat(c: *mut _Z3_context, n: u32, args: *const *mut _Z3_ast) -> *mut _Z3_ast;


        pub unsafe fn Z3_get_app_decl(c: *mut _Z3_context, a: *mut _Z3_app) -> *mut _Z3_func_decl;
        pub unsafe fn Z3_func_decl_to_ast(c: *mut _Z3_context, f: *mut _Z3_func_decl) -> *mut _Z3_ast;

        pub unsafe fn Z3_mk_tactic(c: *mut _Z3_context, name: *const c_char) -> *mut _Z3_tactic;
        pub unsafe fn Z3_tactic_dec_ref(c: *mut _Z3_context, g: *mut _Z3_tactic);
        pub unsafe fn Z3_tactic_inc_ref(c: *mut _Z3_context, g: *mut _Z3_tactic);
        pub unsafe fn Z3_tactic_get_help(c: *mut _Z3_context, t: *mut _Z3_tactic) -> *const c_char;

        pub unsafe fn Z3_model_dec_ref(c: *mut _Z3_context, m: *mut _Z3_model);
        pub unsafe fn Z3_model_inc_ref(c: *mut _Z3_context, m: *mut _Z3_model);
        pub unsafe fn Z3_model_translate(c: *mut _Z3_context, m: *mut _Z3_model, dst: *mut _Z3_context) -> *mut _Z3_model;

        // z3_optimization.h
        pub unsafe fn Z3_mk_optimize(c: *mut _Z3_context) -> *mut _Z3_optimize;
        pub unsafe fn Z3_optimize_get_reason_unknown(c: *mut _Z3_context, d: *mut _Z3_optimize) -> *const c_char;
        pub unsafe fn Z3_optimize_to_string(c: *mut _Z3_context, o: *mut _Z3_optimize) -> *const c_char;
        pub unsafe fn Z3_optimize_dec_ref(c: *mut _Z3_context, d: *mut _Z3_optimize);
        pub unsafe fn Z3_optimize_inc_ref(c: *mut _Z3_context, d: *mut _Z3_optimize);
        pub unsafe fn Z3_optimize_get_objectives(c: *mut _Z3_context, o: *mut _Z3_optimize) -> *mut _Z3_ast_vector;
        pub unsafe fn Z3_optimize_check(c: *mut _Z3_context, o: *mut _Z3_optimize, num_assumptions: u32, assumptions: *const *mut _Z3_ast) -> Z3_lbool;
        pub unsafe fn Z3_optimize_pop(c: *mut _Z3_context, d: *mut _Z3_optimize);
        pub unsafe fn Z3_optimize_push(c: *mut _Z3_context, d: *mut _Z3_optimize);
        pub unsafe fn Z3_optimize_minimize(c: *mut _Z3_context, o: *mut _Z3_optimize, t: *mut _Z3_ast) -> u32;
        pub unsafe fn Z3_optimize_maximize(c: *mut _Z3_context, o: *mut _Z3_optimize, t: *mut _Z3_ast) -> u32;
        pub unsafe fn Z3_optimize_assert_soft(c: *mut _Z3_context, o: *mut _Z3_optimize, a: *mut _Z3_ast, weight: *const c_char, id: *mut _Z3_symbol) -> u32;
        pub unsafe fn Z3_optimize_assert(c: *mut _Z3_context, o: *mut _Z3_optimize, a: *mut _Z3_ast);
        pub unsafe fn Z3_optimize_get_model(c: *mut _Z3_context, o: *mut _Z3_optimize) -> *mut _Z3_model;


        // z3_ast_containers.h
        pub unsafe fn Z3_ast_vector_get(c: *mut _Z3_context, v: *mut _Z3_ast_vector, i: u32) -> *mut _Z3_ast;
        pub unsafe fn Z3_ast_vector_size(c: *mut _Z3_context, v: *mut _Z3_ast_vector) -> u32;

        // z3_
        pub unsafe fn Z3_mk_fpa_numeral_float(c: *mut _Z3_context, v: f32, ty: *mut _Z3_sort) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_fpa_numeral_double(c: *mut _Z3_context, v: f64, ty: *mut _Z3_sort) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_fpa_div(c: *mut _Z3_context, rm: *mut _Z3_ast, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_fpa_mul(c: *mut _Z3_context, rm: *mut _Z3_ast, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_fpa_sub(c: *mut _Z3_context, rm: *mut _Z3_ast, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_fpa_add(c: *mut _Z3_context, rm: *mut _Z3_ast, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;

        pub unsafe fn Z3_mk_fpa_gt(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_fpa_lt(c: *mut _Z3_context, t1: *mut _Z3_ast, t2: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_fpa_neg(c: *mut _Z3_context, t: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_fpa_abs(c: *mut _Z3_context, t: *mut _Z3_ast) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_fpa_round_toward_positive(c: *mut _Z3_context) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_fpa_round_toward_negative(c: *mut _Z3_context) -> *mut _Z3_ast;
        pub unsafe fn Z3_mk_fpa_round_toward_zero(c: *mut _Z3_context) -> *mut _Z3_ast;
        pub unsafe fn Z3_fpa_get_sbits(c: *mut _Z3_context, s: *mut _Z3_sort) -> u32;
        pub unsafe fn Z3_fpa_get_ebits(c: *mut _Z3_context, s: *mut _Z3_sort) -> u32;
        pub unsafe fn Z3_mk_fpa_sort(c: *mut _Z3_context, ebits: u32, sbits: u32) -> *mut _Z3_sort;
    }
}

pub type Z3_string = *const ::std::os::raw::c_char;
pub type Z3_context = *mut ffi::_Z3_context;
pub type Z3_config = *mut ffi::_Z3_config;
pub type Z3_symbol = *mut ffi::_Z3_symbol;
pub type Z3_ast = *mut ffi::_Z3_ast;
pub type Z3_app = *mut ffi::_Z3_app;
pub type Z3_pattern = *mut ffi::_Z3_pattern;
pub type Z3_probe = *mut ffi::_Z3_probe;
pub type Z3_goal = *mut ffi::_Z3_goal;
pub type Z3_tactic = *mut ffi::_Z3_tactic;
pub type Z3_apply_result = *mut ffi::_Z3_apply_result;
pub type Z3_params = *mut ffi::_Z3_params;
pub type Z3_func_decl = *mut ffi::_Z3_func_decl;
pub type Z3_optimize = *mut ffi::_Z3_optimize;
pub type Z3_model = *mut ffi::_Z3_model;
pub type Z3_solver = *mut ffi::_Z3_solver;
pub type Z3_sort = *mut ffi::_Z3_sort;
pub type Z3_constructor = *mut ffi::_Z3_constructor;
pub type Z3_constructor_list = *mut ffi::_Z3_constructor_list;
