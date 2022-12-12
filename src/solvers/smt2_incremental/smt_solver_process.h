// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_SOLVER_PROCESS_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_SOLVER_PROCESS_H

class smt_commandt;

#include <util/message.h>
#include <util/piped_process.h>

#include <solvers/smt2_incremental/ast/smt_responses.h>

#include <memory>
#include <sstream>
#include <string>

class smt_base_solver_processt
{
public:
  virtual std::string description() = 0;

  /// \brief Converts given SMT2 command to SMT2 string and sends it to the
  ///    solver process.
  virtual void send(const smt_commandt &smt_command);

  virtual smt_responset
  receive_response(const std::unordered_map<irep_idt, smt_identifier_termt>
                     &identifier_table) = 0;

  virtual ~smt_base_solver_processt() = default;

protected:
  virtual void send(const std::string &)
  {
  }
};

class smt_piped_solver_processt : public virtual smt_base_solver_processt
{
public:
  /// \param command_line:
  ///   The command and arguments for invoking the smt2 solver.
  /// \param message_handler:
  ///   The messaging system to be used for logging purposes.
  smt_piped_solver_processt(
    std::string command_line,
    message_handlert &message_handler);

  std::string description() override;

  smt_responset receive_response(
    const std::unordered_map<irep_idt, smt_identifier_termt> &identifier_table)
    override;

  ~smt_piped_solver_processt() override = default;

protected:
  void send(const std::string &command_string) override;

  /// The command line used to start the process.
  std::string command_line_description;
  /// The raw solver sub process.
  piped_processt process;
  /// For buffering / combining communications from the solver to cbmc.
  std::stringstream response_stream;
  /// For debug printing.
  messaget log;
};

/// Class for an incremental SMT solver used in combination with `--outfile`
///    argument where the solver is never run.
class smt_incremental_dry_run_solvert : public virtual smt_base_solver_processt
{
public:
  /// \param out_stream:
  ///   Reference to the stream to print the SMT formula.
  /// \param file_stream:
  ///   Pointer to the file stream to print the SMT formula into. `nullptr` if
  ///     output is to `std::cout`.
  smt_incremental_dry_run_solvert(
    std::ostream &out_stream,
    std::unique_ptr<std::ostream> file_stream);

  std::string description() override;

  /// \note This function returns always a valid unsat response.
  smt_responset receive_response(
    const std::unordered_map<irep_idt, smt_identifier_termt> &identifier_table)
    override;

  ~smt_incremental_dry_run_solvert() override = default;

protected:
  void send(const std::string &smt_command) override;

  /// Pointer to the file stream to print the SMT formula. `nullptr` if output
  ///    is to `std::cout`.
  std::unique_ptr<std::ostream> file_stream;
  /// The output stream reference to print the SMT formula to.
  std::ostream &out_stream;
};

class smt_piped_solver_process_with_dumpt : public smt_piped_solver_processt,
                                            smt_incremental_dry_run_solvert
{
public:
  /// \param command_line:
  ///   The command and arguments for invoking the smt2 solver.
  /// \param message_handler:
  ///   The messaging system to be used for logging purposes.
  /// \param out_stream:
  ///   Pointer to the stream to print the SMT formula.
  smt_piped_solver_process_with_dumpt(
    std::string command_line,
    message_handlert &message_handler,
    std::unique_ptr<std::ostream> out_stream);

  void send(const std::string &smt_command) override;

  std::string description() override;

  smt_responset receive_response(
    const std::unordered_map<irep_idt, smt_identifier_termt> &identifier_table)
    override;

  ~smt_piped_solver_process_with_dumpt() override = default;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_SOLVER_PROCESS_H
