// Author: Diffblue Ltd.

/// \file
/// Decision procedure with incremental SMT2 solving.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT2_INCREMENTAL_DECISION_PROCEDURE_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT2_INCREMENTAL_DECISION_PROCEDURE_H

#include <util/message.h>
#include <util/std_expr.h>

#include <solvers/smt2_incremental/object_tracking.h>
#include <solvers/smt2_incremental/smt_object_size.h>
#include <solvers/smt2_incremental/smt_terms.h>
#include <solvers/stack_decision_procedure.h>

#include <memory>
#include <unordered_map>
#include <unordered_set>

class smt_commandt;
class message_handlert;
class namespacet;
class smt_base_solver_processt;

class smt2_incremental_decision_proceduret final
  : public stack_decision_proceduret
{
public:
  /// \param _ns: Namespace for looking up the expressions which symbol_exprts
  ///   relate to.
  /// \param solver_process:
  ///   The smt2 solver process communication interface.
  /// \param message_handler:
  ///   The messaging system to be used for logging purposes.
  explicit smt2_incremental_decision_proceduret(
    const namespacet &_ns,
    std::unique_ptr<smt_base_solver_processt> solver_process,
    message_handlert &message_handler);

  // Implementation of public decision_proceduret member functions.
  exprt handle(const exprt &expr) override;
  exprt get(const exprt &expr) const override;
  void print_assignment(std::ostream &out) const override;
  std::string decision_procedure_text() const override;
  std::size_t get_number_of_solver_calls() const override;
  void set_to(const exprt &expr, bool value) override;

  // Implementation of public stack_decision_proceduret member functions.
  void push(const std::vector<exprt> &assumptions) override;
  void push() override;
  void pop() override;

protected:
  // Implementation of protected decision_proceduret member function.
  resultt dec_solve() override;
  /// \brief Defines any functions which \p expr depends on, which have not yet
  ///   been defined, along with their dependencies in turn.
  void define_dependent_functions(const exprt &expr);
  void ensure_handle_for_expr_defined(const exprt &expr);
  /// \brief Add objects in \p expr to object_map if needed and convert to smt.
  /// \note This function is non-const because it mutates the object_map.
  smt_termt convert_expr_to_smt(const exprt &expr);

  const namespacet &ns;

  size_t number_of_solver_calls;

  std::unique_ptr<smt_base_solver_processt> solver_process;
  messaget log;

  class sequencet
  {
    size_t next_id = 0;

  public:
    size_t operator()()
    {
      return next_id++;
    }
  } handle_sequence;

  std::unordered_map<exprt, smt_identifier_termt, irep_hash>
    expression_handle_identifiers;
  std::unordered_map<exprt, smt_identifier_termt, irep_hash>
    expression_identifiers;
  smt_object_mapt object_map;
  smt_object_sizet object_size_function;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT2_INCREMENTAL_DECISION_PROCEDURE_H
