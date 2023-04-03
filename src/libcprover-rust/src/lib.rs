#![doc = include_str!("../readme.md")]
#![warn(missing_docs)]

/// The main API module for interfacing with CProver tools (`cbmc`, `goto-analyzer`, etc).
#[cxx::bridge]
pub mod cprover_api {

    // The following two definitions for enums are *shared types* - in
    // contrast to the opaque types. These are supposed to match the
    // definitions on the C++ side, and `cxx.rs` will generate static
    // assertions to make sure that these are extern enums that match
    // the definitions on the C++ side (i.e. it will treat C++ as the
    // source of truth rather than Rust).

    /// This type reflects the success of the whole verification run.
    /// E.g. If all of the assertions have been passing, then the result is
    /// going to be `PASS` - if there's just one failing, the verification
    /// result will be `FAIL`. You can get `UNKNOWN` only in the case where
    /// you request verification results before running the verification
    /// engine (not possible through the Rust interface) and `ERROR` if there
    /// is something that causes the SAT solver to fail.
    #[derive(Debug)]
    #[repr(i32)]
    enum verifier_resultt {
        /// The verification engine run hasn't been run yet.
        UNKNOWN,
        /// No properties were violated.
        PASS,
        /// Some properties were violated.
        FAIL,
        /// An error occured during the running of the solver.
        ERROR,
    }

    /// This type is similar to [verifier_resultt] above, but reflects the
    /// status of a single property checked.
    #[derive(Debug)]
    #[repr(i32)]
    enum prop_statust {
        /// The property was not checked.
        NOT_CHECKED,
        /// The checker was unable to determine the status of the property.
        UNKNOWN,
        /// The property was proven to be unreachable.
        NOT_REACHABLE,
        /// The property was not violated.
        PASS,
        /// The property was violated.
        FAIL,
        /// An error occured in the solver during checking the property's status.
        ERROR,
    }

    unsafe extern "C++" {
        include!("api.h");
        include!("verification_result.h");

        include!("include/c_api.h");

        /// Central organisational handle of the API. This directly corresponds to the
        /// C++-API type `api_sessiont`. To initiate a session interaction, call [new_api_session].
        type api_sessiont;

        type verifier_resultt;
        type prop_statust;

        /// This type acts as an opaque handle to the verification results object.
        /// This will be given back to us through a UniquePtr, which we pass into
        /// the functions that will give us back the results in a more granular level:
        /// * [get_verification_result] will give the full verification engine run result,
        /// * [get_property_ids] will give the list of property identifiers of the model,
        /// * [get_property_description] will give a string description for a property identifier
        /// * [get_property_status] will give the status of a property for a given identifier.
        type verification_resultt;

        /// Provide a unique pointer to the API handle. This will be required to interact
        /// with the API calls, and thus, is expected to be the first call before any other
        /// interaction with the API.
        fn new_api_session() -> UniquePtr<api_sessiont>;

        /// Return the API version - note that this is coming from the C++ API, which
        /// returns the API version of CBMC (which should map to the version of `libcprover.a`)
        /// the Rust API has mapped against.
        fn get_api_version(self: &api_sessiont) -> UniquePtr<CxxString>;
        /// Provided a C++ Vector of Strings (use [translate_vector_of_string] to translate
        /// a Rust `Vec<String` into a `CxxVector<CxxString>` before passing it to the function),
        /// load the models from the files in the vector and link them together.
        fn load_model_from_files(self: &api_sessiont, files: &CxxVector<CxxString>) -> Result<()>;
        /// Execute a verification engine run against the loaded model.
        /// *ATTENTION*: A model must be loaded before this function is run.
        fn verify_model(self: &api_sessiont) -> Result<UniquePtr<verification_resultt>>;
        /// Run a validation check on the goto-model that has been loaded.
        /// Corresponds to the CProver CLI option `--validate-goto-model`.
        fn validate_goto_model(self: &api_sessiont) -> Result<()>;
        /// Drop functions that aren't used from the model. Corresponds to
        /// the CProver CLI option `--drop-unused-functions`
        fn drop_unused_functions(self: &api_sessiont) -> Result<()>;

        /// Gets a pointer to the opaque type describing the aggregate verification results and
        /// returns an enum value of type [verifier_resultt] representing the whole of the verification
        /// engine run.
        fn get_verification_result(result: &UniquePtr<verification_resultt>) -> verifier_resultt;
        /// Gets a pointer to the opaque type describing the aggregate verification results
        /// and returns a C++ Vector of C++ Strings containing the identifiers of the
        /// properties present in the model.
        fn get_property_ids(result: &UniquePtr<verification_resultt>) -> &CxxVector<CxxString>;
        /// Given a pointer to the opaque type representing the aggregate verification results
        /// and a property identifier using a C++ string (you can use `cxx:let_cxx_string` to
        /// declare), returns a C++ string that contains the property description.
        /// If a bad identifier is given, this returns an `Result::Err`.
        fn get_property_description<'a>(
            result: &'a UniquePtr<verification_resultt>,
            property_id: &CxxString,
        ) -> Result<&'a CxxString>;
        /// Given a pointer to the opaque type representing the aggregate verification results
        /// and a property identifier using a C++ string (you can use `cxx:let_cxx_string` to
        /// declare), returns a value of type [prop_statust] that contains the individual
        /// property's status.
        /// If a bad identifier is given, this returns an `Result::Err`.
        fn get_property_status(
            result: &UniquePtr<verification_resultt>,
            property_id: &CxxString,
        ) -> Result<prop_statust>;

        // WARNING: Please don't use this function - use its public interface in [ffi_util::translate_rust_vector_to_cpp].
        // The reason this is here is that it's implemented on the C++ shim, and to link this function against
        // its implementation it needs to be declared within the `unsafe extern "C++"` block of the FFI bridge.
        #[doc(hidden)]
        fn _translate_vector_of_string(elements: Vec<String>) -> &'static CxxVector<CxxString>;
        /// Print messages accumulated into the message buffer from CProver's end.
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
    /// from CBMC's C++ API.
    pub fn print_response(vec: &Vec<String>) {
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

// To test run "CBMC_LIB_DIR=<path_to_build/libs> CBMC_VERSION=<version> cargo test -- --test-threads=1 --nocapture"
#[cfg(test)]
mod tests {
    use cprover_api::prop_statust;
    use cprover_api::verifier_resultt;

    use super::*;
    use cxx::let_cxx_string;
    use std::process;

    #[test]
    fn it_works() {
        let client = cprover_api::new_api_session();
        let result = client.get_api_version();

        let_cxx_string!(expected_version = "5.79.0");
        assert!(*result > *expected_version);
    }

    #[test]
    fn translate_vector_of_rust_string_to_cpp() {
        let vec: Vec<String> = vec!["other/example.c".to_owned(), "/tmp/example2.c".to_owned()];

        let vect = ffi_util::translate_rust_vector_to_cpp(vec);
        assert_eq!(vect.len(), 2);
    }

    // This test will capture a `system_exceptiont` from CBMC's end at the C++ shim that this
    // library depends on, and it will be correctly translated into the Result type for Rust.
    // This also validates that our type definition include of the base class for the exceptions
    // works as we expect it to.
    #[test]
    fn it_translates_exceptions_to_errors() {
        let client = cprover_api::new_api_session();

        // The vector of string is supposed to contain a string denoting
        // a filepath that is erroneous.
        let vec: Vec<String> = vec!["/fkjsdlkjfisudifoj2309".to_owned()];
        let vect = ffi_util::translate_rust_vector_to_cpp(vec);

        assert!(client.load_model_from_files(vect).is_err());
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

        // ffi_util::print_response(msgs_assert);
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

    #[test]
    fn it_can_produce_verification_results_for_file() -> Result<(), String> {
        let binding = cprover_api::new_api_session();
        let client = match binding.as_ref() {
            Some(api_ref) => api_ref,
            None => panic!("Failed to acquire API session handle"),
        };

        let vec: Vec<String> = vec!["other/example.c".to_owned()];

        let vect = ffi_util::translate_rust_vector_to_cpp(vec);
        assert_eq!(vect.len(), 1);

        if let Err(_) = client.load_model_from_files(vect) {
            let error_msg = format!("Failed to load GOTO model from files: {:?}", vect).to_string();
            return Err(error_msg);
        }

        // Perform a drop of any unused functions.
        if let Err(err) = client.drop_unused_functions() {
            let error_msg = format!("Error during API call: {:?}", err).to_string();
            return Err(error_msg);
        }

        let results = client.verify_model();
        if let Ok(el) = results {
            let verifier_results = cprover_api::get_verification_result(&el);
            match verifier_results {
                verifier_resultt::FAIL => Ok(()),
                _ => Err("Unexpected result from verification engine run".to_string()),
            }
        } else {
            Err("Unable to produce results from the verification engine".to_string())
        }
    }

    #[test]
    fn it_can_query_property_identifiers_from_result() -> Result<(), String> {
        let binding = cprover_api::new_api_session();
        let client = match binding.as_ref() {
            Some(api_ref) => api_ref,
            None => panic!("Failed to acquire API session handle"),
        };

        let vec: Vec<String> = vec!["other/example.c".to_owned()];

        let vect = ffi_util::translate_rust_vector_to_cpp(vec);
        assert_eq!(vect.len(), 1);

        if let Err(_) = client.load_model_from_files(vect) {
            let error_msg = format!("Failed to load GOTO model from files: {:?}", vect).to_string();
            return Err(error_msg);
        }

        let results = client.verify_model();
        if let Ok(el) = results {
            let property_ids_cxx = cprover_api::get_property_ids(&el);
            let property_ids_rust = ffi_util::translate_cpp_vector_to_rust(property_ids_cxx);
            let expected_property_id = "main.assertion.1";
            if property_ids_rust.contains(&expected_property_id.to_owned()) {
                Ok(())
            } else {
                let error_msg = format!(
                    "Unable to find expected assertion id in model: {}",
                    expected_property_id
                )
                .to_string();
                Err(error_msg)
            }
        } else {
            Err("Unable to produce results from the verification engine".to_string())
        }
    }

    #[test]
    fn it_can_get_the_property_description_for_existing_property() -> Result<(), String> {
        let binding = cprover_api::new_api_session();
        let client = match binding.as_ref() {
            Some(api_ref) => api_ref,
            None => panic!("Failed to acquire API session handle"),
        };

        let vec: Vec<String> = vec!["other/example.c".to_owned()];

        let vect = ffi_util::translate_rust_vector_to_cpp(vec);
        assert_eq!(vect.len(), 1);

        if let Err(_) = client.load_model_from_files(vect) {
            let error_msg = format!("Failed to load GOTO model from files: {:?}", vect).to_string();
            return Err(error_msg);
        }

        let results = client.verify_model();
        if let Ok(el) = results {
            let_cxx_string!(existing_property_id = "main.assertion.1");
            let description = cprover_api::get_property_description(&el, &existing_property_id);
            if let Ok(description_text) = description {
                assert_eq!(description_text, "expected failure: arr[3] == 3");
                Ok(())
            } else {
                let error_msg = format!(
                    "Unable to get description for property {:?}",
                    &existing_property_id
                );
                Err(error_msg)
            }
        } else {
            Err("Unable to produce results from the verification engine".to_string())
        }
    }

    #[test]
    fn it_raises_an_exception_when_getting_the_property_description_for_nonexisting_property(
    ) -> Result<(), String> {
        let binding = cprover_api::new_api_session();
        let client = match binding.as_ref() {
            Some(api_ref) => api_ref,
            None => panic!("Failed to acquire API session handle"),
        };

        let vec: Vec<String> = vec!["other/example.c".to_owned()];

        let vect = ffi_util::translate_rust_vector_to_cpp(vec);
        assert_eq!(vect.len(), 1);

        if let Err(_) = client.load_model_from_files(vect) {
            let error_msg = format!("Failed to load GOTO model from files: {:?}", vect).to_string();
            return Err(error_msg);
        }

        let results = client.verify_model();
        if let Ok(el) = results {
            let_cxx_string!(non_existing_property = "main.the.jabberwocky");
            if let Err(_) = cprover_api::get_property_description(&el, &non_existing_property) {
                Ok(())
            } else {
                let error_msg = format!(
                    "Got a description for non-existent property {:?}",
                    &non_existing_property
                );
                Err(error_msg)
            }
        } else {
            Err("Unable to produce results from the verification engine".to_string())
        }
    }

    #[test]
    fn it_can_get_the_property_status_for_existing_property() -> Result<(), String> {
        let binding = cprover_api::new_api_session();
        let client = match binding.as_ref() {
            Some(api_ref) => api_ref,
            None => panic!("Failed to acquire API session handle"),
        };

        let vec: Vec<String> = vec!["other/example.c".to_owned()];

        let vect = ffi_util::translate_rust_vector_to_cpp(vec);
        assert_eq!(vect.len(), 1);

        if let Err(_) = client.load_model_from_files(vect) {
            let error_msg = format!("Failed to load GOTO model from files: {:?}", vect);
            return Err(error_msg);
        }

        let results = client.verify_model();
        if let Ok(el) = results {
            let_cxx_string!(existing_property_id = "main.assertion.1");
            let prop_status = cprover_api::get_property_status(&el, &existing_property_id);
            match prop_status {
                Ok(prop_statust::FAIL) => Ok(()),
                _ => {
                    let error_msg = format!(
                        "Property status for property {:?} was {:?} - expected FAIL",
                        existing_property_id, prop_status
                    );
                    Err(error_msg)
                }
            }
        } else {
            Err("Unable to produce results from the verification engine".to_string())
        }
    }

    #[test]
    fn it_raises_an_exception_when_getting_status_of_non_existing_property() -> Result<(), String> {
        let binding = cprover_api::new_api_session();
        let client = match binding.as_ref() {
            Some(api_ref) => api_ref,
            None => panic!("Failed to acquire API session handle"),
        };

        let vec: Vec<String> = vec!["other/example.c".to_owned()];

        let vect = ffi_util::translate_rust_vector_to_cpp(vec);
        assert_eq!(vect.len(), 1);

        if let Err(_) = client.load_model_from_files(vect) {
            let error_msg = format!("Failed to load GOTO model from files: {:?}", vect);
            return Err(error_msg);
        }

        let results = client.verify_model();
        if let Ok(el) = results {
            let_cxx_string!(non_existing_property = "main.the.jabberwocky");
            let prop_status = cprover_api::get_property_status(&el, &non_existing_property);
            if let Err(status) = prop_status {
                Ok(())
            } else {
                let error_msg = format!(
                    "Produced verification status for non-existing property: {:?}",
                    non_existing_property
                );
                Err(error_msg)
            }
        } else {
            Err("Unable to produce results from the verification engine".to_string())
        }
    }
}
