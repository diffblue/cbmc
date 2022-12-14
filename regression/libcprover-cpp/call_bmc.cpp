// Author: Fotis Koutoulakis for Diffblue Ltd.

// Test file to try loading a GOTO-model into memory and running a sample verification run on it.
#include <util/exception_utils.h>

#include <libcprover-cpp/api.h>
#include <libcprover-cpp/options.h>

#include "goto_model.h"

#include <iostream>
#include <vector>

void print_messages_to_stdout(
  const api_messaget &message,
  api_call_back_contextt)
{
  std::cout << api_message_get_string(message) << std::endl;
}

int main(int argc, char *argv[])
{
  try
  {
    std::cout << "Hello from API stub" << std::endl;

    // Convert argv to vector of strings for initialize_goto_model
    std::vector<std::string> arguments(argv + 1, argv + argc);

    // Create API options object, to pass to initialiser of API object.
    auto api_options = api_optionst::create()
                         .simplify(false)
                         .validate_goto_model(true)
                         .drop_unused_functions(true);

    // Initialise API dependencies and global configuration in one step.
    api_sessiont api(api_options);

    // Demonstrate the loading of a goto-model from the command line arguments
    api.set_message_callback(print_messages_to_stdout, nullptr);
    api.load_model_from_files(arguments);

    std::cout << "Successfully initialised goto_model" << std::endl;

    // Demonstrate the validation of an already loaded goto-model
    api.validate_goto_model();

    std::cout << "Successfully validated goto_model" << std::endl;

    // Demonstrate the dropping of unused functions from an already loaded
    // goto-model
    api.drop_unused_functions();

    std::cout << "Successfully dropped unused functions from goto_model"
              << std::endl;

    return 0;
  }
  catch(const invalid_command_line_argument_exceptiont &e)
  {
    std::cout << e.what() << std::endl;
  }
}
