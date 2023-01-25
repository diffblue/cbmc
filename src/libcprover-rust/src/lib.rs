use cxx::{CxxVector, CxxString};
#[cxx::bridge]
pub mod ffi {

    unsafe extern "C++" {
        include!("libcprover-cpp/api.h");
        include!("include/c_api.h");

        type api_sessiont;

        // API Functions
        fn new_api_session() -> UniquePtr<api_sessiont>;
        fn get_api_version(&self) -> UniquePtr<CxxString>;
        fn load_model_from_files(&self, files: &CxxVector<CxxString>);
        fn verify_model(&self);
        fn validate_goto_model(&self);
        fn drop_unused_functions(&self);

        // Helper/Utility functions
        fn translate_vector_of_string(elements: Vec<String>) -> &'static CxxVector<CxxString>;
        fn get_messages() -> &'static CxxVector<CxxString>;
    }

    extern "Rust" {
        fn print_response(vec: &CxxVector<CxxString>);
    }
}

fn print_response(vec: &CxxVector<CxxString>) {
    let vec: Vec<String> = vec
        .iter()
        .map(|s| s.to_string_lossy().into_owned())
        .collect();
    
    for s in vec {
        println!("{}", s);
    }
}

// To test run "CBMC_LIB_DIR=<path_to_build/libs> cargo test -- --test-threads=1 --nocapture"
#[cfg(test)]
mod tests {
    use super::*;
    use cxx::let_cxx_string;

    #[test]
    fn it_works() {
        let client = ffi::new_api_session();
        let result = client.get_api_version();

        let_cxx_string!(expected_version = "0.1");
        assert_eq!(*result, *expected_version);
    }

    #[test]
    fn translate_vector_of_rust_string_to_cpp() {
        let vec: Vec<String> = vec![
            "other/example.c".to_owned(),
            "/tmp/example2.c".to_owned()];

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
    
        let vec: Vec<String> = vec![
            "other/example.c".to_owned()];

        let vect = ffi::translate_vector_of_string(vec);
        assert_eq!(vect.len(), 1);

        // Invoke load_model_from_files and see if the model
        // has been loaded.
        client.load_model_from_files(vect);
        // Validate integrity of passed goto-model.
        client.validate_goto_model();

        let msgs = ffi::get_messages();
        print_response(msgs);
    }

    #[test]
    fn it_can_verify_the_loaded_model() {        
        let client = ffi::new_api_session();
    
        let vec: Vec<String> = vec![
            "other/example.c".to_owned()];

        let vect = ffi::translate_vector_of_string(vec);
        client.load_model_from_files(vect);

        // Validate integrity of goto-model
        client.validate_goto_model();

        client.verify_model();

        let msgs = ffi::get_messages();
        print_response(msgs);
    }

    #[test]
    fn it_can_drop_unused_functions_from_model() {
        let binding = ffi::new_api_session();
        let client = match binding.as_ref() {
            Some(api_ref) => api_ref,
            None => panic!("Failed to acquire API session handle"),
        };
    
        let vec: Vec<String> = vec![
            "other/example.c".to_owned()];

        let vect = ffi::translate_vector_of_string(vec);
        assert_eq!(vect.len(), 1);

        client.load_model_from_files(vect);
        // Perform a drop of any unused functions.
        client.drop_unused_functions();

        let msgs = ffi::get_messages();
        print_response(msgs);
    }
}
