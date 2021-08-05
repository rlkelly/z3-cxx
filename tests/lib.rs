extern crate z3_cxx;

use z3_cxx::ffi::{
    _Z3_config,
    Z3_mk_config,
    Z3_global_param_reset_all,
};

#[test]
fn smoketest() {
    unsafe {
        let config: *mut _Z3_config = Z3_mk_config();
        Z3_global_param_reset_all();
    }
}
