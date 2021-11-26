// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_SOLVER_PROCESS_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_SOLVER_PROCESS_H

class smt_commandt;

#include <solvers/smt2_incremental/smt_responses.h>
#include <util/message.h>
#include <util/piped_process.h>

#include <sstream>
#include <string>

class smt_base_solver_processt
{
public:
  virtual const std::string &description() = 0;

  /// \brief Converts given SMT2 command to SMT2 string and sends it to the
  ///    solver process.
  virtual void send(const smt_commandt &command) = 0;

  virtual smt_responset receive_response() = 0;

  virtual ~smt_base_solver_processt() = default;
};

class smt_piped_solver_processt : public smt_base_solver_processt
{
public:
  /// \param command_line:
  ///   The command and arguments for invoking the smt2 solver.
  /// \param message_handler:
  ///   The messaging system to be used for logging purposes.
  smt_piped_solver_processt(
    std::string command_line,
    message_handlert &message_handler);

  const std::string &description() override;

  void send(const smt_commandt &smt_command) override;

  smt_responset receive_response() override;

  ~smt_piped_solver_processt() override = default;

protected:
  /// The command line used to start the process.
  std::string command_line_description;
  /// The raw solver sub process.
  piped_processt process;
  /// For buffering / combining communications from the solver to cbmc.
  std::stringstream response_stream;
  /// For debug printing.
  messaget log;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_SOLVER_PROCESS_H
