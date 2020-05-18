/*******************************************************************\

Module: Show function pointer values

Author: Diffblue Ltd, 2020

\*******************************************************************/

#ifndef CPROVER_GOTO_ANALYZER_GET_FUNCTION_POINTER_VALUES_H
#define CPROVER_GOTO_ANALYZER_GET_FUNCTION_POINTER_VALUES_H

#include <util/nodiscard.h>

#include <goto-programs/restrict_function_pointers.h>

class goto_modelt;
class ai_baset;
class message_handlert;

#define OPT_GET_FUNCTION_POINTER_VALUES "(get-function-pointer-values):"

/// Get function pointer restrictions that have been obtained via abstract
/// interpretation with value sets in the variable sensitivity domain.
/// \param goto_model The goto model that was analysed
/// \param ai The abstract interpreter, needs to have run with the
///           variable sensitivity domain with value sets turned on
/// \param message_handler For printing debug messages
NODISCARD function_pointer_restrictionst
get_function_pointer_restrictions_from_value_set_ai(
  const goto_modelt &goto_model,
  const ai_baset &ai,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_ANALYZER_GET_FUNCTION_POINTER_VALUES_H
