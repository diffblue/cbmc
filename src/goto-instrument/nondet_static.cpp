/*******************************************************************\

Module: Nondeterministically initializes global scope variables, except for
 constants (such as string literals, final fields) and internal variables
 (such as CPROVER and symex variables, language specific internal
 variables).

Author: Daniel Kroening, Michael Tautschnig

Date: November 2011

\*******************************************************************/

/// \file
/// Nondeterministically initializes global scope variables, except for
/// constants (such as string literals, final fields) and internal variables
/// (such as CPROVER and symex variables, language specific internal
/// variables).

#include "nondet_static.h"

#include <goto-programs/goto_model.h>

#include <linking/static_lifetime_init.h>

/// See the return.
/// \param symbol_expr: The symbol expression to analyze.
/// \param ns: Namespace for resolving type information
/// \return True if the symbol expression holds a static symbol which can be
/// nondeterministically initialized, false otherwise.
bool is_nondet_initializable_static(
  const symbol_exprt &symbol_expr,
  const namespacet &ns)
{
  const irep_idt &id = symbol_expr.get_identifier();

  // is it a __CPROVER_* variable?
  if(has_prefix(id2string(id), CPROVER_PREFIX))
    return false;

  // variable not in symbol table such as symex variable?
  if(!ns.get_symbol_table().has_symbol(id))
    return false;

  const symbolt &symbol = ns.lookup(id);

  // is the type explicitly marked as not to be nondet initialized?
  if(symbol.type.get_bool(ID_C_no_nondet_initialization))
    return false;

  // is the type explicitly marked as not to be initialized?
  if(symbol.type.get_bool(ID_C_no_initialization_required))
    return false;

  // static lifetime?
  if(!symbol.is_static_lifetime)
    return false;

  // constant?
  return !is_constant_or_has_constant_components(symbol_expr.type(), ns) &&
         !is_constant_or_has_constant_components(symbol.type, ns);
}

/// Nondeterministically initializes global scope variables in a goto-function.
/// Iterates over instructions in the specified function and replaces all values
/// assigned to nondet-initializable static variables with nondeterministic
/// values.
/// \param ns: Namespace for resolving type information.
/// \param [out] goto_functions: Existing goto-functions to be updated.
/// \param fct_name: Name of the goto-function to be updated.
void nondet_static(
  const namespacet &ns,
  goto_functionst &goto_functions,
  const irep_idt &fct_name)
{
  goto_functionst::function_mapt::iterator fct_entry =
    goto_functions.function_map.find(fct_name);
  CHECK_RETURN(fct_entry != goto_functions.function_map.end());

  goto_programt &init = fct_entry->second.body;

  Forall_goto_program_instructions(i_it, init)
  {
    const goto_programt::instructiont &instruction=*i_it;

    if(instruction.is_assign())
    {
      const symbol_exprt &sym=to_symbol_expr(
          to_code_assign(instruction.code).lhs());

      if(is_nondet_initializable_static(sym, ns))
      {
        const goto_programt::instructiont original_instruction = instruction;
        i_it->make_assignment();
        i_it->code = code_assignt(
          sym,
          side_effect_expr_nondett(
            sym.type(), original_instruction.source_location));
        i_it->source_location = original_instruction.source_location;
        i_it->function = original_instruction.function;
      }
    }
    else if(instruction.is_function_call())
    {
      const code_function_callt &fct=to_code_function_call(instruction.code);
      const symbol_exprt &fsym=to_symbol_expr(fct.function());

      if(has_prefix(id2string(fsym.get_identifier()), "#ini#"))
        nondet_static(ns, goto_functions, fsym.get_identifier());
    }
  }
}

/// Nondeterministically initializes global scope variables in
/// CPROVER_initialize function.
/// \param ns: Namespace for resolving type information.
/// \param [out] goto_functions: Existing goto-functions to be updated.
void nondet_static(
  const namespacet &ns,
  goto_functionst &goto_functions)
{
  nondet_static(ns, goto_functions, INITIALIZE_FUNCTION);

  // update counters etc.
  goto_functions.update();
}

/// Main entry point of the module. Nondeterministically initializes global
/// scope variables, except for constants (such as string literals, final
/// fields) and internal variables (such as CPROVER and symex variables,
/// language specific internal variables).
/// \param [out] goto_model: Existing goto-model to be updated.
void nondet_static(goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);
  nondet_static(ns, goto_model.goto_functions);
}
