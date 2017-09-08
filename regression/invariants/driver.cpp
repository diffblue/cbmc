/*******************************************************************\

Module: Invariant violation testing

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Invariant violation testing

#include <string>
#include <sstream>

#include <util/invariant.h>
#include <util/invariant_utils.h>
#include <util/std_types.h>
#include <util/c_types.h>

/// An example of structured invariants-- this contains fields to
/// describe the error to a catcher, and also produces a human-readable
/// message containing all the information for use by the current aborting
/// invariant implementation and/or any generic error catcher in the future.
class structured_error_testt: public invariant_failedt
{
  std::string pretty_print(int code, const std::string &desc)
  {
    std::ostringstream ret;
    ret << "Error code: " << code
        << "\nDescription: " << desc;
    return ret.str();
  }

public:
  const int error_code;
  const std::string description;

  structured_error_testt(
    const std::string &file,
    const std::string &function,
    int line,
    const std::string &backtrace,
    int code,
    const std::string &_description):
    invariant_failedt(
      file,
      function,
      line,
      backtrace,
      pretty_print(code, _description)),
    error_code(code),
    description(_description)
  {
  }
};

/// Causes an invariant failure dependent on first argument value.
/// One ignored argument is accepted to conform with the test.pl script,
/// which would be the input source file for other cbmc driver programs.
/// Returns 1 on unexpected arguments.
int main(int argc, char** argv)
{
  if(argc!=3)
    return 1;
  std::string arg=argv[1];
  if(arg=="structured")
    INVARIANT_STRUCTURED(false, structured_error_testt, 1, "Structured error"); // NOLINT
  else if(arg=="string")
    INVARIANT(false, "Test invariant failure");
  else if(arg=="precondition-structured")
    PRECONDITION_STRUCTURED(false, structured_error_testt, 1, "Structured error"); // NOLINT
  else if(arg=="precondition-string")
    PRECONDITION(false);
  else if(arg=="postcondition-structured")
    POSTCONDITION_STRUCTURED(false, structured_error_testt, 1, "Structured error"); // NOLINT
  else if(arg=="postcondition-string")
    POSTCONDITION(false);
  else if(arg=="check-return-structured")
    CHECK_RETURN_STRUCTURED(false, structured_error_testt, 1, "Structured error"); // NOLINT
  else if(arg=="check-return-string")
    CHECK_RETURN(false);
  else if(arg=="unreachable-structured")
    UNREACHABLE_STRUCTURED(structured_error_testt, 1, "Structured error"); // NOLINT
  else if(arg=="unreachable-string")
    UNREACHABLE;
  else if(arg=="data-invariant-structured")
    DATA_INVARIANT_STRUCTURED(false, structured_error_testt, 1, "Structured error"); // NOLINT
  else if(arg=="data-invariant-string")
    DATA_INVARIANT(false, "Test invariant failure");
  else if(arg=="irep")
    INVARIANT_WITH_IREP(false, "error with irep", pointer_type(void_typet()));
  else
    return 1;
}
