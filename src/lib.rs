use cxx;

#[cxx::bridge]
pub mod ffi {

    unsafe extern "C++" {
        include!("z3-cxx/include/z3.h");

        type _Z3_config;
        pub fn Z3_mk_config() -> *mut _Z3_config;
    }
}
