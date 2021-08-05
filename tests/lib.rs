extern crate z3cxx2;

use std::ffi::{CStr, CString};
use z3cxx2::ffi::{
    _Z3_config,
    Z3_mk_config,
};

#[test]
fn smoketest() {
    unsafe {
        Z3_mk_config();
    }
}
