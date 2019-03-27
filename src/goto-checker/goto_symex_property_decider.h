/*******************************************************************\

Module: Property Decider for Goto-Symex

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Property Decider for Goto-Symex

#ifndef CPROVER_GOTO_CHECKER_GOTO_SYMEX_PROPERTY_DECIDER_H
#define CPROVER_GOTO_CHECKER_GOTO_SYMEX_PROPERTY_DECIDER_H

#include <util/ui_message.h>

#include <goto-symex/symex_target_equation.h>

#include "properties.h"
#include "solver_factory.h"

/// Provides management of goal variables that encode properties
class goto_symex_property_decidert
{
public:
  goto_symex_property_decidert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    symex_target_equationt &equation,
    const namespacet &ns);

  /// Get the conditions for the properties from the equation
  /// and collect all 'instances' of the properties in the `goal_map`
  void
  update_properties_goals_from_symex_target_equation(propertiest &properties);

  /// Convert the instances of a property into a goal variable
  void convert_goals();

  /// Prevent the solver to optimize-away the goal variables
  /// (necessary for incremental solving)
  void freeze_goal_variables();

  /// Add disjunction of negated selected properties to the equation
  void add_constraint_from_goals(
    std::function<bool(const irep_idt &property_id)> select_property);

  /// Calls solve() on the solver instance
  decision_proceduret::resultt solve();

  /// Returns the solver instance
  decision_procedure_incrementalt &get_solver() const;

  /// Return the equation associated with this instance
  symex_target_equationt &get_equation() const;

  /// Update the property status from the truth value of the goal variable
  /// \param [inout] properties: The status is updated in this data structure
  /// \param [inout] updated_properties: The set of property IDs of
  ///   updated properties
  /// \param dec_result: The result returned by the solver
  /// \param set_pass: If true then update UNKNOWN properties to PASS
  ///   if the solver returns UNSATISFIABLE
  void update_properties_status_from_goals(
    propertiest &properties,
    std::unordered_set<irep_idt> &updated_properties,
    decision_proceduret::resultt dec_result,
    bool set_pass = true) const;

protected:
  const optionst &options;
  ui_message_handlert &ui_message_handler;
  symex_target_equationt &equation;
  std::unique_ptr<solver_factoryt::solvert> solver;
  decision_procedure_incrementalt *decision_procedure = nullptr;

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
};

#endif // CPROVER_GOTO_CHECKER_GOTO_SYMEX_PROPERTY_DECIDER_H
