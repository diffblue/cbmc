# CProver (CBMC) Rust API

This folder contains the implementation of the Rust API of the CProver (CBMC) project.

## Building instructions

There are two ways to build the project:

1. As part of the CBMC project (using `cmake`) by building CBMC with the flag
   `-DWITH_RUST_API=ON`. The outcome of this process is a compilation artefact
   `libcprover-x.y.z.a` under the `<build>/lib` directory.
2. By executing `cargo build` under this (`src/libcprover-rust`) directory.

   For this to work, you need to supply two environment variables to the
   project:

   * `CBMC_LIB_DIR`, for selecting where the `libcprover-x.y.z.a` is located
     (say, if you have downloaded a pre-packaged release which contains
      the static library), and
   * `CBMC_VERSION`, for selecting the version of the library to link against
     (this is useful if you have multiple versions of the library in the same
      location and you want to control which version you compile against).

As an example, a command sequence to build the API through `cargo` would look
like this (assuming you're executing these instructions from the root level
directory of the CBMC project.)

```sh
$ cd src/libcprover-rust
$ cargo clean
$ CBMC_LIB_DIR=../../build/lib CBMC_VERSION=5.78.0 cargo build
```

To build the project and run its associated tests, the command sequence would
look like this:

```sh
$ cd src/libcprover-rust
$ cargo clean
$ CBMC_LIB_DIR=../../build/lib CBMC_VERSION=5.78.0 cargo test -- --test-threads=1 --nocapture
```

## Notes

* The functions supported by the Rust API are catalogued within the `ffi` module within
  `lib.rs`.
* The API supports exception handling from inside CBMC by catching the exceptions in
  a C++ shim, and then translating the exception into the Rust `Result` type.
* Because of limitations from the C++ side of CBMC, the API is not thread-safe.
