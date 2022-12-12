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
  message_handlert &message_handler,
  std::unique_ptr<std::ostream> out_stream)
  : command_line_description{"\"" + command_line + "\""},
    out_stream(std::move(out_stream)),
    process{split_string(command_line, ' ', false, true), message_handler},
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

  if(out_stream != nullptr)
  {
    // Using `std::endl` instead of '\n' to also flush the stream as it is a
    // debugging functionality, to guarantee a consistent output in case of
    // hanging after `(check-sat)`
    *out_stream << command_string << std::endl;
  }

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

smt_responset smt_piped_solver_processt::receive_response(
  const std::unordered_map<irep_idt, smt_identifier_termt> &identifier_table)
{
  const auto response_text = process.wait_receive();
  log.debug() << "Solver response - " << response_text << messaget::eom;
  response_stream << response_text;
  const auto parse_tree = smt2irep(response_stream, log.get_message_handler());
  if(!parse_tree)
    throw deserialization_exceptiont{"Incomplete SMT response."};
  const auto validation_result =
    validate_smt_response(*parse_tree, identifier_table);
  if(const auto validation_errors = validation_result.get_if_error())
    handle_invalid_smt(*validation_errors, log);
  return *validation_result.get_if_valid();
}

smt_incremental_dry_run_solvert::smt_incremental_dry_run_solvert(
  std::ostream &out_stream,
  std::unique_ptr<std::ostream> file_stream)
  : file_stream(std::move(file_stream)), out_stream(out_stream)
{
}

const std::string &smt_incremental_dry_run_solvert::description()
{
  return desc;
}

void smt_incremental_dry_run_solvert::send(const smt_commandt &smt_command)
{
  out_stream << smt_to_smt2_string(smt_command) << '\n';
}

smt_responset smt_incremental_dry_run_solvert::receive_response(
  const std::unordered_map<irep_idt, smt_identifier_termt> &identifier_table)
{
  // Using `smt_unsat_responset` as response because the decision-procedure will
  // terminate anyway (stop-on-fail), it is not reported to the user as for
  // `unknown`, and does not trigger a subsequent invocation to get the model
  // (as a `smt_sat_responset` answer will trigger).
  return smt_check_sat_responset{smt_unsat_responset{}};
}
