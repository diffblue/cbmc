/*******************************************************************\
Module: Label function pointer call sites
Author: Diffblue Ltd.
\*******************************************************************/

/// \file
/// Label function pointer call sites across a goto model
/// \see simplify_function_pointers

#ifndef CPROVER_GOTO_PROGRAMS_LABEL_FUNCTION_POINTER_CALL_SITES_H
#define CPROVER_GOTO_PROGRAMS_LABEL_FUNCTION_POINTER_CALL_SITES_H

#include "goto_model.h"

/// This ensures that call instructions can be only one of two things:
///
/// 1. A "normal" function call to a concrete function
/// 2. A dereference of a symbol expression of a function pointer type
///
/// This makes following stages dealing with function calls easier, because they
/// only need to be able to handle these two cases.
///
/// It does this by replacing all CALL instructions to function pointers with an
/// assignment to a new function pointer variable followed by a call to that new
/// function pointer. The name of the introduced variable follows the pattern
/// [function_name].function_pointer_call.[N], where N is the nth call to a
/// function pointer in the function function_name.
void label_function_pointer_call_sites(goto_modelt &goto_model);

#endif // CPROVER_GOTO_PROGRAMS_LABEL_FUNCTION_POINTER_CALL_SITES_H
