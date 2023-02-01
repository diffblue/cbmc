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

fn get_cadical_build_dir() -> std::io::Result<PathBuf> {
    let env_var_fetch_result = get_build_directory();
    if let Ok(build_dir) = env_var_fetch_result {
        let mut path = PathBuf::new();
        path.push(build_dir);
        path.push("cadical-src/build/");
        return Ok(path);
    }
    Err(Error::new(
        ErrorKind::Other,
        "failed to get build output directory",
    ))
}

fn get_sat_library() -> std::io::Result<&'static str> {
    let env_var_name = "SAT_IMPL";
    let env_var_fetch_result = env::var(env_var_name);
    if let Ok(sat_impl) = env_var_fetch_result {
        let solver_lib = match sat_impl.as_str() {
            "minisat2" => Ok("minisat2-condensed"),
            "glucose" => Ok("glucose-condensed"),
            "cadical" => Ok("cadical"),
            _ => Err(Error::new(
                ErrorKind::Other,
                "no identifiable solver detected",
            )),
        };
        return solver_lib;
    }
    Err(Error::new(
        ErrorKind::Other,
        "SAT_IMPL environment variable not set",
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

    let solver_lib = match get_sat_library() {
        Ok(solver) => solver,
        Err(err) => panic!("Error: {}", err),
    };

    // Cadical is being built in its own directory, with the resultant artefacts being
    // present only there. Hence, we need to instruct cargo to look for them in cadical's
    // build directory, otherwise we're going to get build errors.
    if solver_lib == "cadical" {
        let cadical_build_dir = match get_cadical_build_dir() {
            Ok(cadical_directory) => cadical_directory,
            Err(err) => panic!("Error: {}", err),
        };
        println!(
            "cargo:rustc-link-search=native={}",
            cadical_build_dir.display()
        );
    }

    println!(
        "cargo:rustc-link-search=native={}",
        libraries_path.display()
    );
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
    println!("cargo:rustc-link-lib=static={}", solver_lib);
    println!("cargo:rustc-link-lib=static=cbmc-lib");
    println!("cargo:rustc-link-lib=static=cprover-api-cpp");
}
