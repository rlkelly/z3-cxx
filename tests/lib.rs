extern crate z3_cxx;

use std::ffi::{CStr, CString};

use z3_cxx::ffi::{
    Z3_mk_config,
    Z3_del_config,

    Z3_mk_context,
    Z3_del_context,

    Z3_global_param_reset_all,
    Z3_mk_string_symbol,
    Z3_mk_int_sort,
    Z3_mk_const,
    Z3_mk_gt,
    Z3_mk_simple_solver,
    Z3_solver_assert,
    Z3_solver_check,
    Z3_solver_get_model,
    Z3_model_to_string,
    Z3_model_eval,

    Z3_get_numeral_int,
};

use z3_cxx::{
    Z3_config,
    Z3_context,
    Z3_ast,
    Z3_L_TRUE,
    Z3_TRUE,
};

#[test]
fn smoketest() {
    unsafe {
        let config: Z3_config = Z3_mk_config();
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

        let model = Z3_solver_get_model(ctx, solver);

        // Check that the string-value of the model is as expected
        let model_s = Z3_model_to_string(ctx, model);
        assert_eq!(
            CStr::from_ptr(model_s).to_str().unwrap(),
            "x -> 0\ny -> (- 1)\n"
        );

        // Grab the actual constant values out of the model
        let mut interp_x: Z3_ast = const_x;
        let mut interp_y: Z3_ast = const_y;
        assert_eq!(
            Z3_model_eval(ctx, model, const_x, Z3_TRUE, &mut interp_x),
            Z3_TRUE
        );
        assert_eq!(
            Z3_model_eval(ctx, model, const_y, Z3_TRUE, &mut interp_y),
            Z3_TRUE
        );

        let mut val_x: i32 = -5;
        let mut val_y: i32 = -5;
        assert_eq!(Z3_get_numeral_int(ctx, interp_x, &mut val_x), Z3_TRUE);
        assert_eq!(Z3_get_numeral_int(ctx, interp_y, &mut val_y), Z3_TRUE);
        assert_eq!(val_x, 0);
        assert_eq!(val_y, -1);

        Z3_del_context(ctx);
        Z3_del_config(config);
    }
}
