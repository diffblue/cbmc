// Author: Diffblue Ltd.

#include <solvers/smt2_incremental/smt_solver_process.h>

#include <solvers/smt2/smt2irep.h>
#include <solvers/smt2_incremental/smt_response_validation.h>
#include <solvers/smt2_incremental/smt_to_smt2_string.h>
#include <util/exception_utils.h>
#include <util/invariant.h>
#include <util/string_utils.h>

smt_piped_solver_processt::smt_piped_solver_processt(
  std::string command_line,
  message_handlert &message_handler)
  : command_line_description{"\"" + command_line + "\""},
    process{split_string(command_line, ' ', false, true)},
    log{message_handler}
{
}

const std::string &smt_piped_solver_processt::description()
{
  return command_line_description;
}

void smt_piped_solver_processt::send(const smt_commandt &smt_command)
{
  const std::string command_string = smt_to_smt2_string(smt_command);
  log.debug() << "Sending command to SMT2 solver - " << command_string
              << messaget::eom;
  const auto response = process.send(command_string + "\n");
  switch(response)
  {
  case piped_processt::send_responset::SUCCEEDED:
    return;
  case piped_processt::send_responset::FAILED:
    throw analysis_exceptiont{"Sending to SMT solver sub process failed."};
  case piped_processt::send_responset::ERRORED:
    throw analysis_exceptiont{"SMT solver sub process is in error state."};
  }
  UNREACHABLE;
}

/// Log messages and throw exception.
static void handle_invalid_smt(
  const std::vector<std::string> &validation_errors,
  messaget &log)
{
  for(const std::string &message : validation_errors)
  {
    log.error() << message << messaget::eom;
  }
  throw analysis_exceptiont{"Invalid SMT response received from solver."};
}

smt_responset smt_piped_solver_processt::receive_response()
{
  const auto response_text = process.wait_receive();
  log.debug() << "Solver response - " << response_text << messaget::eom;
  response_stream << response_text;
  const auto parse_tree = smt2irep(response_stream, log.get_message_handler());
  if(!parse_tree)
    throw deserialization_exceptiont{"Incomplete SMT response."};
  const auto validation_result = validate_smt_response(*parse_tree);
  if(const auto validation_errors = validation_result.get_if_error())
    handle_invalid_smt(*validation_errors, log);
  return *validation_result.get_if_valid();
}
