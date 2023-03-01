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

fn get_sat_libraries() -> std::io::Result<Vec<&'static str>> {
    let env_var_name = "SAT_IMPL";
    let env_var_fetch_result = env::var(env_var_name);
    if let Ok(sat_impls) = env_var_fetch_result {
        let mut solver_libs = Vec::new();
        for sat_impl in sat_impls.split(" ") {
            let solver_lib = match sat_impl {
                "minisat2" => "minisat2-condensed",
                "glucose" => "glucose-condensed",
                "cadical" => "cadical",
                _ => {
                    return Err(Error::new(
                        ErrorKind::Other,
                        "no identifiable solver detected",
                    ))
                }
            };
            solver_libs.push(solver_lib);
        }
        return Ok(solver_libs);
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

    let solver_libs = match get_sat_libraries() {
        Ok(solvers) => solvers,
        Err(err) => panic!("Error: {}", err),
    };

    for solver_lib in solver_libs.iter() {
        // Cadical is being built in its own directory, with the resultant artefacts being
        // present only there. Hence, we need to instruct cargo to look for them in cadical's
        // build directory, otherwise we're going to get build errors.
        if *solver_lib == "cadical" {
            let cadical_build_dir = match get_cadical_build_dir() {
                Ok(cadical_directory) => cadical_directory,
                Err(err) => panic!("Error: {}", err),
            };
            println!(
                "cargo:rustc-link-search=native={}",
                cadical_build_dir.display()
            );
        }
    }

    println!(
        "cargo:rustc-link-search=native={}",
        libraries_path.display()
    );

    println!("cargo:rustc-link-lib=static=cprover.5.77.0");
}
