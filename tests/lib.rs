extern crate z3_cxx;

use z3_cxx::ffi::{
    // _Z3_config,
    Z3_mk_config,
};

#[test]
fn smoketest() {
    unsafe {
        Z3_mk_config();
    }
}
