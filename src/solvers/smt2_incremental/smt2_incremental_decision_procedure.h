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
#include <solvers/smt2_incremental/type_size_mapping.h>
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
  /// \brief Defines a function of array sort and asserts the element values
  /// from `array_exprt` or `array_of_exprt`.
  /// \details
  ///   The new array function identifier is added to the
  ///   `expression_identifiers` map.
  /// \note Statically fails if the template type is not a `array_exprt` or
  /// `array_of_exprt`.
  template <typename t_exprt>
  void define_array_function(const t_exprt &array);
  /// \brief Generate and send to the SMT solver clauses asserting that each
  /// array element is as specified by \p array.
  void initialize_array_elements(
    const array_exprt &array,
    const smt_identifier_termt &array_identifier);
  /// \brief Generate and send to the SMT solver clauses asserting that each
  /// array element is as specified by \p array.
  /// \note This function uses a forall SMT2 term. Using it in combination with
  /// arrays, bit vectors and uninterpreted functions requires the `ALL` SMT
  /// logic that is not in the SMT 2.6 standard, but that it has been tested
  /// working on Z3 and CVC5.
  void initialize_array_elements(
    const array_of_exprt &array,
    const smt_identifier_termt &array_identifier);
  /// \brief Defines any functions which \p expr depends on, which have not yet
  ///   been defined, along with their dependencies in turn.
  void define_dependent_functions(const exprt &expr);
  void ensure_handle_for_expr_defined(const exprt &expr);
  /// \brief Add objects in \p expr to object_map if needed and convert to smt.
  /// \note This function is non-const because it mutates the object_map.
  smt_termt convert_expr_to_smt(const exprt &expr);
  /// Sends the solver the definitions of the object sizes.
  void define_object_sizes();

  /// Namespace for looking up the expressions which symbol_exprts relate to.
  /// This includes the symbols defined outside of the decision procedure but
  /// does not include any additional SMT function identifiers introduced by the
  /// decision procedure.
  const namespacet &ns;
  /// The number of times `dec_solve()` has been called.
  size_t number_of_solver_calls;
  /// \brief For handling the lifetime of and communication with the separate
  ///   SMT solver process.
  /// \note This may be mocked for unit testing purposes.
  std::unique_ptr<smt_base_solver_processt> solver_process;
  /// For reporting errors, warnings and debugging information back to the user.
  messaget log;
  /// Generators of sequences of uniquely identifying numbers used for naming
  /// SMT functions introduced by the decision procedure.
  class sequencet
  {
    size_t next_id = 0;

  public:
    size_t operator()()
    {
      return next_id++;
    }
  } handle_sequence, array_sequence;
  /// When the `handle(exprt)` member function is called, the decision procedure
  /// commands the SMT solver to define a new function corresponding to the
  /// given expression. The mapping of the expressions to the function
  /// identifiers is stored in this map so that when there is as subsequent
  /// `get(exprt)` call for the same expression, the function identifier can be
  /// requested from the solver, rather than reconverting the expression.
  std::unordered_map<exprt, smt_identifier_termt, irep_hash>
    expression_handle_identifiers;
  /// As part of the decision procedure's overall translation of CBMCs `exprt`s
  /// into SMT terms, some subexpressions are substituted for separate SMT
  /// functions. This map associates these sub-expressions to the identifiers of
  /// the separated functions. This applies to `symbol_exprt` where it is fairly
  /// natural to define the value of the symbol using a separate function, but
  /// also to the expressions which define entire arrays. This includes
  /// `array_exprt` for example and will additionally include other similar
  /// array expressions when support for them is implemented.
  std::unordered_map<exprt, smt_identifier_termt, irep_hash>
    expression_identifiers;
  /// This map is used to track object related state. See documentation in
  /// object_tracking.h for details.
  smt_object_mapt object_map;
  /// The size of each object is separately defined as a pre-solving step.
  /// `object_size_defined[object ID]` is set to true for objects where the size
  /// has been defined. This is used to avoid defining the size of the same
  /// object multiple times in the case where multiple rounds of solving are
  /// carried out.
  std::vector<bool> object_size_defined;
  /// Implementation of the SMT formula for the object size function. This is
  /// stateful because it depends on the configuration of the number of object
  /// bits and how many bits wide the size type is configured to be.
  smt_object_sizet object_size_function;
  /// Precalculated type sizes used for pointer arithmetic.
  type_size_mapt pointer_sizes_map;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT2_INCREMENTAL_DECISION_PROCEDURE_H
