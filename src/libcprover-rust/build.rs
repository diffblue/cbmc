use std::env;
use std::io::{Error, ErrorKind};
use std::path::Path;
use std::path::PathBuf;

fn get_current_working_dir() -> std::io::Result<PathBuf> {
    env::current_dir()
}

fn get_library_build_dir() -> std::io::Result<PathBuf> {
    let env_var_name = "CBMC_LIB_DIR";
    let env_var_fetch_result = env::var(env_var_name);
    if let Ok(lib_dir) = env_var_fetch_result {
        let mut path = PathBuf::new();
        path.push(lib_dir);
        return Ok(path);
    }
    Err(Error::new(ErrorKind::Other, "failed to get library output directory"))
}

fn get_sat_library() -> &'static str {
    let env_var_name = "SAT_IMPL";
    let env_var_fetch_result = env::var(env_var_name);
    if let Ok(sat_impl) = env_var_fetch_result {
        let solver_lib = match sat_impl.as_str() {
            "minisat2" => "minisat2-condensed",
            "glucose"  => "libglucose-condensed",
            "cadical"  => "cadical",
            _          => "Error: no identifiable solver detected"
        };
        return solver_lib;
    }
    "Error: no identifiable solver detected"
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
        Err(err) => panic!("{}", err)
    };

    println!("cargo:rustc-link-search=native={}", libraries_path.display());
    println!("cargo:rustc-link-lib=static=goto-programs");
    println!("cargo:rustc-link-lib=static=util");
    println!("cargo:rustc-link-lib=static=langapi");
    println!("cargo:rustc-link-lib=static=ansi-c");
    println!("cargo:rustc-link-lib=static=analyses");
    println!("cargo:rustc-link-lib=static=goto-instrument-lib");
    println!("cargo:rustc-link-lib=static=big-int");
    println!("cargo:rustc-link-lib=static=linking");
    println!("cargo:rustc-link-lib=static=goto-checker");
    println!("cargo:rustc-link-lib=static=solvers");
    println!("cargo:rustc-link-lib=static=assembler");
    println!("cargo:rustc-link-lib=static=xml");
    println!("cargo:rustc-link-lib=static=json");
    println!("cargo:rustc-link-lib=static=json-symtab-language");
    println!("cargo:rustc-link-lib=static=cpp");
    println!("cargo:rustc-link-lib=static=jsil");
    println!("cargo:rustc-link-lib=static=statement-list");
    println!("cargo:rustc-link-lib=static=goto-symex");
    println!("cargo:rustc-link-lib=static=pointer-analysis");
    println!("cargo:rustc-link-lib=static={}", get_sat_library());
    println!("cargo:rustc-link-lib=static=cbmc-lib");
    println!("cargo:rustc-link-lib=static=cprover-api-cpp");
}
