use cxx;

#[cxx::bridge]
pub mod ffi {
    unsafe extern "C++" {
        include!("z3_cxx/include/z3_inc.h");

        type _Z3_config;
        fn Z3_global_param_reset_all();
        pub fn Z3_mk_config() -> *mut _Z3_config;
    }
}
