extern crate z3_cxx;

use std::ffi::{CStr, CString};

use z3_cxx::ffi::{
    Z3_mk_config,
    Z3_del_config,
    Z3_mk_context,
    Z3_global_param_reset_all,
    Z3_mk_string_symbol,
    Z3_mk_int_sort,
    Z3_mk_const,
    Z3_mk_gt,
    Z3_mk_simple_solver,
    Z3_solver_assert,
    Z3_solver_check,
};

use z3_cxx::{
    Z3_config,
    Z3_context,
    Z3_L_TRUE,
};

#[test]
fn smoketest() {
    unsafe {
        let config: Z3_config = Z3_mk_config();
        Z3_del_config(config);
        let ctx: Z3_context = Z3_mk_context(config);

        let str_x = CString::new("x").unwrap();
        let str_y = CString::new("y").unwrap();

        // TODO: cxx.rs wants these to be *mut but bindgen and the C++ code uses *const
        let sym_x = Z3_mk_string_symbol(ctx, str_x.into_raw());
        let sym_y = Z3_mk_string_symbol(ctx, str_y.into_raw());

        let int_sort = Z3_mk_int_sort(ctx);

        let const_x = Z3_mk_const(ctx, sym_x, int_sort);
        let const_y = Z3_mk_const(ctx, sym_y, int_sort);
        let gt = Z3_mk_gt(ctx, const_x, const_y);

        let solver = Z3_mk_simple_solver(ctx);
        Z3_solver_assert(ctx, solver, gt);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);
    }
}
