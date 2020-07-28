/*******************************************************************\

Module: value_set_fi_Fp_removal

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// flow insensitive value set function pointer removal

#ifndef CPROVER_GOTO_INSTRUMENT_VALUE_SET_FI_FP_REMOVAL_H
#define CPROVER_GOTO_INSTRUMENT_VALUE_SET_FI_FP_REMOVAL_H

class goto_modelt;
class message_handlert;
/// Builds the flow-insensitive value set for all function pointers
/// and replaces function pointers with a non-deterministic switch
/// between this set. If the set is empty, the function pointer is
/// not removed. Thus remove_function_pointers should be run after this to
// guarantee removal of all function pointers.
/// \param goto_model: goto model to be modified
/// \param message_handler: message handler for status output
void value_set_fi_fp_removal(
  goto_modelt &goto_model,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_INSTRUMENT_VALUE_SET_FI_FP_REMOVAL_H
