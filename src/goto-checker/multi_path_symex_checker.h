/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Multi-Path Symbolic Execution

#ifndef CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_CHECKER_H
#define CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_CHECKER_H

#include "goto_trace_provider.h"
#include "multi_path_symex_only_checker.h"
#include "solver_factory.h"
#include "witness_provider.h"

/// Performs a multi-path symbolic execution using goto-symex
/// and calls a SAT/SMT solver to check the status of the properties.
class multi_path_symex_checkert : public multi_path_symex_only_checkert,
                                  public goto_trace_providert,
                                  public witness_providert
{
public:
  multi_path_symex_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  /// \copydoc incremental_goto_checkert::operator()(propertiest &properties)
  ///
  /// Note: Repeated invocations of this operator with properties P_1, P_2, ...
  ///   must satisfy the condition 'P_i contains P_i+1'.
  ///   I.e. after checking properties P_i the caller may decide to check
  ///   only a subset of properties P_i+1 in the following invocation,
  ///   but the caller may not add properties to P_i+1 that have not been
  ///   in P_i. Such additional properties will be ignored.
  resultt operator()(propertiest &) override;

  goto_tracet build_trace() const override;
  const namespacet &get_namespace() const override;

  void output_error_witness(const goto_tracet &) override;
  void output_proof() override;

protected:
  std::unique_ptr<solver_factoryt::solvert> solver;

  struct goalt
  {
    /// A property holds if all instances of it are true
    std::vector<symex_target_equationt::SSA_stepst::iterator> instances;

    /// The goal variable
    literalt condition;

    exprt as_expr() const;
  };

  /// Maintains the relation between a property ID and
  /// the corresponding goal variable that encodes
  /// the negation of the conjunction of the instances of the property
  std::map<irep_idt, goalt> goal_map;

  bool equation_generated;

  /// Get the conditions for the properties from the equation
  /// and collect all 'instances' of the properties in the `goal_map`
  void
  update_properties_goals_from_symex_target_equation(propertiest &properties);

  /// Convert the instances of a property into a goal variable
  void convert_goals();

  /// Prevent the solver to optimize-away the goal variables
  /// (necessary for incremental solving)
  void freeze_goal_variables();

  /// Add disjunction of negated properties to the equation
  void add_constraint_from_goals(const propertiest &properties);

  /// Update the property status from the truth value of the goal variable
  /// \param [inout] properties: The status is updated in this data structure
  /// \param [inout] updated_properties: The set of property IDs of
  ///   updated properties
  /// \param dec_result: The result returned by the solver
  void update_properties_status_from_goals(
    propertiest &properties,
    std::unordered_set<irep_idt> &updated_properties,
    decision_proceduret::resultt dec_result);
};

#endif // CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_CHECKER_H
