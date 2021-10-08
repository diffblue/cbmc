// Author: Diffblue Ltd.

#include <solvers/smt2_incremental/smt_solver_process.h>

#include <solvers/smt2_incremental/smt_to_smt2_string.h>
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
  process.send(command_string + "\n");
}

smt_responset smt_piped_solver_processt::receive_response()
{
  const auto response_text = process.wait_receive();
  log.debug() << "Solver response - " << response_text << messaget::eom;
  UNIMPLEMENTED_FEATURE("parsing of solver response.");
}
