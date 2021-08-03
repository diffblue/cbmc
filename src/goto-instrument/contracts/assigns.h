/*******************************************************************\

Module: Specify write set in function contracts.

Author: Felipe R. Monteiro

Date: July 2021

\*******************************************************************/

/// \file
/// Specify write set in function contracts

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_ASSIGNS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_ASSIGNS_H

#include "contracts.h"

#include <ansi-c/expr2c.h>
#include <util/pointer_offset_size.h>

/// \brief A base class for assigns clause targets
class assigns_clause_targett
{
public:
  assigns_clause_targett(
    const exprt &object_ptr,
    code_contractst &contract,
    messaget &log_parameter,
    const irep_idt &function_id);
  ~assigns_clause_targett();

  std::vector<symbol_exprt> temporary_declarations() const;
  exprt alias_expression(const exprt &lhs);
  exprt compatible_expression(const assigns_clause_targett &called_target);
  goto_programt havoc_code(source_locationt location) const;
  const exprt &get_direct_pointer() const;
  goto_programt &get_init_block();

  static exprt pointer_for(const exprt &exp)
  {
    return address_of_exprt(exp);
  }

protected:
  const exprt pointer_object;
  const code_contractst &contract;
  goto_programt init_block;
  messaget &log;
  symbol_exprt local_target;
};

class assigns_clauset
{
public:
  assigns_clauset(
    const exprt &assigns,
    code_contractst &contract,
    const irep_idt function_id,
    messaget log_parameter);
  ~assigns_clauset();

  assigns_clause_targett *add_target(exprt target);
  assigns_clause_targett *add_pointer_target(exprt current_operation);
  goto_programt init_block(source_locationt location);
  goto_programt &temporary_declarations(
    source_locationt location,
    irep_idt function_name,
    irep_idt language_mode);
  goto_programt dead_stmts(
    source_locationt location,
    irep_idt function_name,
    irep_idt language_mode);
  goto_programt havoc_code(
    source_locationt location,
    irep_idt function_name,
    irep_idt language_mode);
  exprt alias_expression(const exprt &lhs);

  exprt compatible_expression(const assigns_clauset &called_assigns);

protected:
  const exprt &assigns_expr;

  std::vector<assigns_clause_targett *> targets;
  goto_programt standin_declarations;

  code_contractst &parent;
  const irep_idt function_id;
  messaget log;
};

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_ASSIGNS_H
