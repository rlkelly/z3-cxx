use cxx;

pub type Z3_bool = bool;
pub const Z3_TRUE: Z3_bool = true;
pub const Z3_FALSE: Z3_bool = false;

#[cxx::bridge]
pub mod ffi {
    unsafe extern "C++" {
        include!("z3_cxx/include/z3_inc.h");

        type _Z3_config;
        type _Z3_context;
        type _Z3_symbol;
        type _Z3_sort;
        type _Z3_ast;
        type _Z3_solver;
        type _Z3_model;

        pub fn Z3_mk_config() -> *mut _Z3_config;
        fn Z3_global_param_reset_all();
    }

    extern "C++" {
        include!("z3_cxx/include/z3_inc.h");

        pub unsafe fn Z3_del_config(c: *mut _Z3_config);
        pub unsafe fn Z3_mk_context(c: *mut _Z3_config) -> *mut _Z3_context;
        pub unsafe fn Z3_del_context(c: *mut _Z3_context);
        pub unsafe fn Z3_mk_string_symbol(
            c: *mut _Z3_context,
            s: *mut c_char,
        ) -> *mut _Z3_symbol;
        pub unsafe fn Z3_mk_int_sort(c: *mut _Z3_context) -> *mut _Z3_sort;
        pub unsafe fn Z3_mk_const(
            c: *mut _Z3_context,
            s: *mut _Z3_symbol,
            ty: *mut _Z3_sort,
        ) -> *mut _Z3_ast;

        pub unsafe fn Z3_mk_gt(
            c: *mut _Z3_context,
            t1: *mut _Z3_ast,
            t2: *mut _Z3_ast,
        ) -> *mut _Z3_ast;

        pub unsafe fn Z3_mk_simple_solver(c: *mut _Z3_context) -> *mut _Z3_solver;
        pub unsafe fn Z3_solver_assert(
            c: *mut _Z3_context, s: *mut _Z3_solver, a: *mut _Z3_ast);
        pub unsafe fn Z3_solver_check(c: *mut _Z3_context, s: *mut _Z3_solver) -> i32;
        pub unsafe fn Z3_solver_get_model(c: *mut _Z3_context, s: *mut _Z3_solver) -> *mut _Z3_model;
        pub unsafe fn Z3_model_to_string(c: *mut _Z3_context, m: *mut _Z3_model) -> *mut c_char;

        pub unsafe fn Z3_model_eval(
            c: *mut _Z3_context,
            m: *mut _Z3_model,
            t: *mut _Z3_ast,
            model_completion: bool,
            v :*mut *mut _Z3_ast,
        ) -> bool;

        pub unsafe fn Z3_get_numeral_int(c: *mut _Z3_context, v: *mut _Z3_ast, i: *mut i32) -> bool;
    }
}

pub type Z3_string = *const ::std::os::raw::c_char;
pub type Z3_context = *mut ffi::_Z3_context;
pub type Z3_config = *mut ffi::_Z3_config;
pub type Z3_symbol = *mut ffi::_Z3_symbol;
pub type Z3_ast = *mut ffi::_Z3_ast;

pub const Z3_L_FALSE: Z3_lbool = -1;
pub const Z3_L_UNDEF: Z3_lbool = 0;
pub const Z3_L_TRUE: Z3_lbool = 1;

/// Lifted Boolean type: `false`, `undefined`, `true`.
pub type Z3_lbool = i32;
