use std::env;
use std::env::VarError;
use std::io::{Error, ErrorKind};
use std::path::Path;
use std::path::PathBuf;

fn get_current_working_dir() -> std::io::Result<PathBuf> {
    env::current_dir()
}

fn get_build_directory() -> Result<String, VarError> {
    env::var("CBMC_BUILD_DIR")
}

fn get_library_build_dir() -> std::io::Result<PathBuf> {
    let env_var_fetch_result = get_build_directory();
    if let Ok(build_dir) = env_var_fetch_result {
        let mut path = PathBuf::new();
        path.push(build_dir);
        path.push("lib/");
        return Ok(path);
    }
    Err(Error::new(
        ErrorKind::Other,
        "failed to get build output directory",
    ))
}

fn main() {
    let cbmc_source_path = Path::new("..");
    let cpp_api_path = Path::new("../libcprover-cpp/");
    let _build = cxx_build::bridge("src/lib.rs")
        .include(cbmc_source_path)
        .include(cpp_api_path)
        .include(get_current_working_dir().unwrap())
        .file("src/c_api.cc")
        .flag_if_supported("-std=c++11")
        .compile("cprover-rust-api");

    println!("cargo:rerun-if-changed=src/c_api.cc");
    println!("cargo:rerun-if-changed=include/c_api.h");

    let libraries_path = match get_library_build_dir() {
        Ok(path) => path,
        Err(err) => panic!("Error: {}", err),
    };

    println!(
        "cargo:rustc-link-search=native={}",
        libraries_path.display()
    );

    println!("cargo:rustc-link-lib=static=cprover.5.78.0");
}
