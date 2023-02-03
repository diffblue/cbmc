use cxx::{CxxString, CxxVector};
#[cxx::bridge]
pub mod ffi {

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

        // Helper/Utility functions
        fn translate_vector_of_string(elements: Vec<String>) -> &'static CxxVector<CxxString>;
        fn get_messages() -> &'static CxxVector<CxxString>;
    }

    extern "Rust" {
        fn print_response(vec: &CxxVector<CxxString>);
        fn translate_response_buffer(vec: &CxxVector<CxxString>) -> Vec<String>;
    }
}

/// This is a utility function, whose job is to translate the responses from the C++
/// API (which we get in the form of a C++ std::vector<std:string>) into a form that
/// can be easily consumed by other Rust programs.
pub fn translate_response_buffer(vec: &CxxVector<CxxString>) -> Vec<String> {
    vec.iter()
        .map(|s| s.to_string_lossy().into_owned())
        .collect()
}

/// This is a utility function, whose aim is to simplify direct printing of the messages
/// that we get from CBMC's C++ API. Underneath, it's using translate_response_buffer
/// to translate the C++ types into Rust types and then prints out the strings contained
/// in the resultant rust vector.
pub fn print_response(vec: &CxxVector<CxxString>) {
    let vec: Vec<String> = translate_response_buffer(vec);

    for s in vec {
        println!("{}", s);
    }
}

// To test run "CBMC_LIB_DIR=<path_to_build/libs> SAT_IMPL=minisat2 cargo test -- --test-threads=1 --nocapture"
#[cfg(test)]
mod tests {
    use super::*;
    use cxx::let_cxx_string;
    use std::process;

    #[test]
    fn it_works() {
        let client = ffi::new_api_session();
        let result = client.get_api_version();

        let_cxx_string!(expected_version = "0.1");
        assert_eq!(*result, *expected_version);
    }

    #[test]
    fn translate_vector_of_rust_string_to_cpp() {
        let vec: Vec<String> = vec!["other/example.c".to_owned(), "/tmp/example2.c".to_owned()];

        let vect = ffi::translate_vector_of_string(vec);
        assert_eq!(vect.len(), 2);
    }

    #[test]
    fn it_can_load_model_from_file() {
        let binding = ffi::new_api_session();
        let client = match binding.as_ref() {
            Some(api_ref) => api_ref,
            None => panic!("Failed to acquire API session handle"),
        };

        let vec: Vec<String> = vec!["other/example.c".to_owned()];

        let vect = ffi::translate_vector_of_string(vec);
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
        let msgs = ffi::get_messages();
        let msgs_assert = translate_response_buffer(msgs).clone();

        assert!(msgs_assert.contains(&String::from(validation_msg)));

        // print_response(msgs);
    }

    #[test]
    fn it_can_verify_the_loaded_model() {
        let client = ffi::new_api_session();

        let vec: Vec<String> = vec!["other/example.c".to_owned()];

        let vect = ffi::translate_vector_of_string(vec);

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

        let msgs = ffi::get_messages();
        let msgs_assert = translate_response_buffer(msgs).clone();

        assert!(msgs_assert.contains(&String::from(verification_msg)));
    }

    #[test]
    fn it_can_drop_unused_functions_from_model() {
        let binding = ffi::new_api_session();
        let client = match binding.as_ref() {
            Some(api_ref) => api_ref,
            None => panic!("Failed to acquire API session handle"),
        };

        let vec: Vec<String> = vec!["other/example.c".to_owned()];

        let vect = ffi::translate_vector_of_string(vec);
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

        let msgs = ffi::get_messages();
        let msgs_assert = translate_response_buffer(msgs).clone();

        assert!(msgs_assert.contains(&String::from(instrumentation_msg)));
        assert!(msgs_assert.contains(&String::from(instrumentation_msg2)));
    }
}
