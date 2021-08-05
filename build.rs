fn main() {
    // Do I need to include all z3 here?
    cxx_build::bridge("src/lib.rs")
        .include("src/z3/src/api/z3_macros.h")
        .include("src/z3/src/api/z3_api.h")
        .file("src/z3/src/api/api_config_params.cpp")
        .flag_if_supported("-std=c++17")
        .compile("z3-cxx");

    println!("cargo:rerun-if-changed=src/lib.rs");
    println!("cargo:rerun-if-changed=include/z3.h");
}
