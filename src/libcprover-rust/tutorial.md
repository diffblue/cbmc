# Libcprover-rust

A Rust interface for convenient interaction with the CProver tools.

## Basic Usage

This file will guide through a sample interaction with the API, under a basic
scenario: *loading a file and verifying the model contained within*.

To begin, we will assume that you have a file under `/tmp/api_example.c`,
with the following contents:

```c
int main(int argc, char *argv[])
{
  int arr[] = {0, 1, 2, 3};
  __CPROVER_assert(arr[3] != 3, "expected failure: arr[3] == 3");
}
```

The first thing we need to do to initiate any interaction with the API
itself is to create a new `api_sessiont` handle by using the function
`new_api_session`:

```rust
let client = cprover_api::new_api_session();
```

Then, we need to add the file to a vector with filenames that indicate
which files we want the verification engine to load the models of:

```rust
let vec: Vec<String> = vec!["/tmp/api_example.c".to_owned()];

let vect = ffi_util::translate_rust_vector_to_cpp(vec);
```

In the above code example, we created a Rust language Vector of Strings
(`vec`). In the next line, we called a utility function from the module
`ffi_util` to translate the Rust `Vec<String>` into the C++ equivalent
`std::vector<std::string>` - this step is essential, as we need to translate
the type into something that the C++ end understands.

These operations are *explicit*: we have opted to force users to translate
between types at the FFI level in order to reduce the "magic" and instill
mental models more compatible with the nature of the language-border (FFI)
work. If we didn't, and we assumed the labour of translating these types
transparently at the API level, we risked mistakes from our end or from the
user end frustrating debugging efforts.

At this point, we have a handle of a C++ vector containing the filenames
of the files we want the CProver verification engine to load. To do so,
we're going to use the following piece of code:

```rust
// Invoke load_model_from_files and see if the model has been loaded.
if let Err(_) = client.load_model_from_files(vect) {
    eprintln!("Failed to load model from files: {:?}", vect);
    process::exit(1);
}
```

The above is an example of a Rust idiom known as a `if let` - it's effectively
a pattern match with just one pattern - we don't match any other case.

What we we do above is two-fold:

* We call the function `load_model_from_files` with the C++ vector (`vect`)
  we prepared before. It's worth noting that this function is being called
  with `client.` - what this does is that it passes the `api_session` handle
  we initialised at the beginning as the first argument to the `load_model_from_files`
  on the C++ API's end.
* We handled the case where the model loading failed for whatever reason from
  the C++ end by catching the error on the Rust side and printing a suitable error
  message and exiting the process gracefully.

---

*Interlude*: **Error Handling**

`cxx.rs` (the FFI bridge we're using to build the Rust API) allows for a mechanism
wherein exceptions from the C++ program can be translated into Rust `Result<>` types
provided suitable infrastructure has been built.

Our Rust API contains a C++ shim which (among other things) intercepts CProver
exceptions (from `cbmc`, etc.) and translates them into a form that the bridge
can then translate to appropriate `Result` types that the Rust clients can use.

This means that, as above, we can use the same Rust idioms and types as we would
use on a purely Rust based codebase to interact with the API.

*All of the API calls* are returning `Result` types such as above.

---

After we have loaded the model, we can proceed to then engage the verification
engine for an analysis run:

```rust
if let Err(_) = client.verify_model() {
    eprintln!("Failed to verify model from files: {:?}", vect);
    process::exit(1);
}
```

While all this is happening, we are collecting the output of the various
phases into a message buffer. We can go forward and print any messages from
that buffer into `stdout`:

```rust
let msgs_cpp = cprover_api::get_messages();
let msgs_rust = ffi_util::translate_cpp_vector_to_rust(msgs_cpp);
ffi_util::print_response(msgs_rust);
```
