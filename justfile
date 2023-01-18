# This is a `justfile`, for the program `just`, a task runner.
# Think of it as a better make for targets that are actions rather than
# files. For more information, look at https://github.com/casey/just

default_build_dir := 'build/'
default_solver := 'minisat2'

# Perform a default (debug) build on MacOS systems under folder `build/`
[macos]
build:
    cmake -S. -B{{default_build_dir}} -DCMAKE_C_COMPILER=/usr/bin/clang -DCMAKE_CXX_COMPILER=/usr/bin/clang++
    cmake --build build -j4

# Perform a default (debug) build on Linux systems under folder `build/`
[linux]
build:
    cmake -S. -B{{default_build_dir}}
    cmake --build build -j4

# Test the Rust API (under src/libcprover-rust/)
test-rust-api: build
    cd src/libcprover-rust;\
    cargo clean;\
    CBMC_BUILD_DIR={{justfile_directory()}}/{{default_build_dir}} SAT_IMPL={{default_solver}} cargo test -- --test-threads=1
