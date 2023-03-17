#[cxx::bridge]
pub mod cprover_api {

    unsafe extern "C++" {
        include!("libcprover-cpp/api.h");
        include!("include/c_api.h");

        type api_sessiont;

        // API Functions
        fn new_api_session() -> UniquePtr<api_sessiont>;
        fn get_api_version(&self) -> UniquePtr<CxxString>;
        fn load_model_from_files(&self, files: &CxxVector<CxxString>) -> Result<()>;
        fn verify_model(&self) -> Result<()>;
        fn validate_goto_model(&self) -> Result<()>;
        fn drop_unused_functions(&self) -> Result<()>;

        // WARNING: Please don't use this function - use its public interface in [ffi_util::translate_rust_vector_to_cpp].
        // The reason this is here is that it's implemented on the C++ shim, and to link this function against
        // its implementation it needs to be declared within the `unsafe extern "C++"` block of the FFI bridge.
        #[doc(hidden)]
        fn _translate_vector_of_string(elements: Vec<String>) -> &'static CxxVector<CxxString>;
        fn get_messages() -> &'static CxxVector<CxxString>;
    }
}

/// Module containing utility functions for translating between types across
/// the FFI boundary.
pub mod ffi_util {
    use crate::cprover_api::_translate_vector_of_string;
    use cxx::CxxString;
    use cxx::CxxVector;

    /// This function translates the responses from the C++ API (which we get in the
    /// form of a C++ std::vector<std:string>) into the equivalent Rust type `Vec<String>`.
    /// Dual to [translate_rust_vector_to_cpp].
    pub fn translate_cpp_vector_to_rust(vec: &CxxVector<CxxString>) -> Vec<String> {
        vec.iter()
            .map(|s| s.to_string_lossy().into_owned())
            .collect()
    }

    /// This function aims to simplify direct printing of the messages that we get
    /// from CBMC's C++ API. Underneath, it's using [translate_cpp_vector_to_rust]
    /// to translate the C++ types into Rust types and then prints out the strings
    /// contained in the resultant Rust vector.
    pub fn print_response(vec: &CxxVector<CxxString>) {
        let vec: Vec<String> = translate_response_buffer(vec);

        for s in vec {
            println!("{}", s);
        }
    }

    /// Translate a Rust `Vec<String>` into a C++ acceptable `std::vector<std::string>`.
    /// Dual to [translate_cpp_vector_to_rust].
    pub fn translate_rust_vector_to_cpp(elements: Vec<String>) -> &'static CxxVector<CxxString> {
        _translate_vector_of_string(elements)
    }
}

// To test run "CBMC_LIB_DIR=<path_to_build/libs> SAT_IMPL=minisat2 cargo test -- --test-threads=1 --nocapture"
#[cfg(test)]
mod tests 
    use super::*;
    use cxx::let_cxx_string;
    use std::process;

    #[test]
    fn it_works() {
        let client = cprover_api::new_api_session();
        let result = client.get_api_version();

        let_cxx_string!(expected_version = "0.1");
        assert_eq!(*result, *expected_version);
    }

    #[test]
    fn translate_vector_of_rust_string_to_cpp() {
        let vec: Vec<String> = vec!["other/example.c".to_owned(), "/tmp/example2.c".to_owned()];

        let vect = ffi_util::translate_rust_vector_to_cpp(vec);
        assert_eq!(vect.len(), 2);
    }

    #[test]
    fn it_can_load_model_from_file() {
        let binding = cprover_api::new_api_session();
        let client = match binding.as_ref() {
            Some(api_ref) => api_ref,
            None => panic!("Failed to acquire API session handle"),
        };

        let vec: Vec<String> = vec!["other/example.c".to_owned()];

        let vect = ffi_util::translate_rust_vector_to_cpp(vec);
        assert_eq!(vect.len(), 1);

        // Invoke load_model_from_files and see if the model
        // has been loaded.
        if let Err(_) = client.load_model_from_files(vect) {
            eprintln!("Failed to load model from files: {:?}", vect);
            process::exit(1);
        }

        // Validate integrity of passed goto-model.
        if let Err(_) = client.validate_goto_model() {
            eprintln!("Failed to validate goto model from files: {:?}", vect);
            process::exit(1);
        }

        // ATTENTION: The following `.clone()` is unneeded - I keep it here in order to
        // make potential printing of the message buffer easier (because of borrowing).
        // This is also why a print instruction is commented out (as a guide for someone
        // else in case they want to inspect the output).
        let validation_msg = "Validating consistency of goto-model supplied to API session";
        let msgs = cprover_api::get_messages();
        let msgs_assert = ffi_util::translate_cpp_vector_to_rust(msgs).clone();

        assert!(msgs_assert.contains(&String::from(validation_msg)));

        // print_response(msgs);
    }

    #[test]
    fn it_can_verify_the_loaded_model() {
        let client = cprover_api::new_api_session();

        let vec: Vec<String> = vec!["other/example.c".to_owned()];

        let vect = ffi_util::translate_rust_vector_to_cpp(vec);

        if let Err(_) = client.load_model_from_files(vect) {
            eprintln!("Failed to load model from files: {:?}", vect);
            process::exit(1);
        }

        // Validate integrity of goto-model
        if let Err(_) = client.validate_goto_model() {
            eprintln!("Failed to validate goto model from files: {:?}", vect);
            process::exit(1);
        }

        if let Err(_) = client.verify_model() {
            eprintln!("Failed to verify model from files: {:?}", vect);
            process::exit(1);
        }

        let verification_msg = "VERIFICATION FAILED";

        let msgs = cprover_api::get_messages();
        let msgs_assert = ffi_util::translate_cpp_vector_to_rust(msgs).clone();

        assert!(msgs_assert.contains(&String::from(verification_msg)));
    }

    #[test]
    fn it_can_drop_unused_functions_from_model() {
        let binding = cprover_api::new_api_session();
        let client = match binding.as_ref() {
            Some(api_ref) => api_ref,
            None => panic!("Failed to acquire API session handle"),
        };

        let vec: Vec<String> = vec!["other/example.c".to_owned()];

        let vect = ffi_util::translate_rust_vector_to_cpp(vec);
        assert_eq!(vect.len(), 1);

        if let Err(_) = client.load_model_from_files(vect) {
            eprintln!("Failed to load model from files: {:?}", vect);
            process::exit(1);
        }

        // Perform a drop of any unused functions.
        if let Err(err) = client.drop_unused_functions() {
            eprintln!("Error during client call: {:?}", err);
            process::exit(1);
        }

        let instrumentation_msg = "Performing instrumentation pass: dropping unused functions";
        let instrumentation_msg2 = "Dropping 8 of 11 functions (3 used)";

        let msgs = cprover_api::get_messages();
        let msgs_assert = ffi_util::translate_cpp_vector_to_rust(msgs).clone();

        assert!(msgs_assert.contains(&String::from(instrumentation_msg)));
        assert!(msgs_assert.contains(&String::from(instrumentation_msg2)));
    }
}
