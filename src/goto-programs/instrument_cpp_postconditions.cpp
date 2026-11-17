/*******************************************************************\

Module: Check C++26 postcondition assertions

Author: Kiro

\*******************************************************************/

/// \file
/// Check the postcondition assertions of C++26 functions on normal exit
/// (N5008 [dcl.contract.func], [basic.contract.eval]).

#include "instrument_cpp_postconditions.h"

#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/fresh_symbol.h>
#include <util/mathematical_expr.h>
#include <util/pointer_expr.h>
#include <util/replace_symbol.h>
#include <util/std_expr.h>
#include <util/suffix.h>
#include <util/symbol_table_base.h>

#include "goto_model.h"

/// The object the result name of \p function_id's postconditions denotes
/// ([dcl.contract.res]/1), with an assignment of the returned value to it
/// added at each SET_RETURN_VALUE of \p body where one is needed; nil for a
/// function returning void.
static exprt result_object(
  const irep_idt &function_id,
  goto_functiont &function,
  const typet &return_type,
  symbol_table_baset &symbol_table)
{
  if(return_type.id() == ID_empty)
    return nil_exprt{};

  // a class object returned through elide_cpp_returned_temporaries' hidden
  // result parameter is the caller's result object
  const symbolt &function_symbol = symbol_table.lookup_ref(function_id);
  if(
    to_code_type(function_symbol.type).return_type().id() == ID_empty &&
    !function.parameter_identifiers.empty() &&
    has_suffix(id2string(function.parameter_identifiers.back()), "#result"))
  {
    const symbolt &result_parameter =
      symbol_table.lookup_ref(function.parameter_identifiers.back());
    return dereference_exprt{result_parameter.symbol_expr()};
  }

  // a scalar, a reference (a pointer here) or a trivially copyable class:
  // the returned value, held in a variable for the checks
  symbolt &result_symbol = get_fresh_aux_symbol(
    return_type,
    id2string(function_id),
    "contract_result",
    function_symbol.location,
    function_symbol.mode,
    symbol_table);
  // a local of the function (not static: a destructor run after the return
  // may call the function again), declared at each return -- not at the
  // start of the body, where instrument_preconditions expects the
  // precondition assertions
  result_symbol.is_static_lifetime = false;
  result_symbol.is_thread_local = true;
  result_symbol.is_file_local = true;
  const symbol_exprt result = result_symbol.symbol_expr();

  for(auto it = function.body.instructions.begin();
      it != function.body.instructions.end();
      ++it)
  {
    if(!it->is_set_return_value())
      continue;
    const exprt value =
      typecast_exprt::conditional_cast(it->return_value(), return_type);
    it->return_value() = result;
    goto_programt::instructiont declaration =
      goto_programt::make_decl(result, it->source_location());
    function.body.insert_before_swap(it, declaration);
    ++it;
    goto_programt::instructiont assignment =
      goto_programt::make_assignment(result, value, it->source_location());
    function.body.insert_before_swap(it, assignment);
    ++it;
  }
  return result;
}

void instrument_cpp_postconditions(goto_modelt &goto_model)
{
  symbol_table_baset &symbol_table = goto_model.symbol_table;
  const symbolt *inflight =
    symbol_table.lookup(CPROVER_PREFIX "cpp_inflight_exception");

  for(auto &[function_id, function] : goto_model.goto_functions.function_map)
  {
    if(!function.body_available())
      continue;
    goto_programt &body = function.body;
    if(body.instructions.empty() || !body.instructions.back().is_end_function())
      continue;
    symbolt *contract =
      symbol_table.get_writeable("contract::" + id2string(function_id));
    if(
      contract == nullptr ||
      !contract->type.get_bool("#cpp_enforce_postconditions"))
    {
      continue;
    }
    // instrument once (a goto binary may be processed again)
    contract->type.remove("#cpp_enforce_postconditions");
    const code_with_contract_typet contract_type =
      to_code_with_contract_type(contract->type);
    if(contract_type.c_ensures().empty())
      continue;

    const typet &return_type = contract_type.return_type();
    const exprt result =
      result_object(function_id, function, return_type, symbol_table);

    // N5008 [expr.call]/9: the postconditions are evaluated when the
    // function exits normally, after the result object is initialized and
    // the local variables are destroyed ([stmt.return]/5), before the
    // parameters are destroyed: at END_FUNCTION, not on an exceptional exit.
    // Every exit jumps to END_FUNCTION; it becomes the first check (the jumps
    // keep their target), and a new END_FUNCTION follows the checks.
    goto_programt::targett end = std::prev(body.instructions.end());
    const source_locationt end_location = end->source_location();
    goto_programt tail;
    for(const auto &clause : contract_type.c_ensures())
    {
      exprt predicate = clause.id() == ID_lambda
                          ? to_lambda_expr(clause).where()
                          : static_cast<const exprt &>(clause);
      if(result.is_not_nil())
      {
        replace_symbolt replace;
        replace.insert(
          symbol_exprt{CPROVER_PREFIX "return_value", return_type}, result);
        replace(predicate);
      }
      // the location carries the property's class and description (set by
      // the C++ front end); a violation contract-terminates the program
      // ([basic.contract.eval]/13), which ends the path
      const source_locationt &location = clause.source_location();
      tail.add(goto_programt::make_assertion(predicate, location));
      tail.add(goto_programt::make_assumption(predicate, location));
    }
    goto_programt::targett new_end =
      tail.add(goto_programt::make_end_function(end_location));
    if(inflight != nullptr)
    {
      *end = goto_programt::make_goto(
        new_end,
        notequal_exprt{
          inflight->symbol_expr(),
          null_pointer_exprt{to_pointer_type(inflight->type)}},
        end_location);
    }
    else
    {
      // no exceptions in the program: the first check replaces END_FUNCTION
      *end = tail.instructions.front();
      tail.instructions.pop_front();
    }
    body.destructive_append(tail);
    body.update();
  }
}
