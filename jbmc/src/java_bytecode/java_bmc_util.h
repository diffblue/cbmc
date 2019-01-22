/*******************************************************************\

Module: Bounded Model Checking Utils for Java

Author: Daniel Kroening, Peter Schrammel

 \*******************************************************************/

/// \file
/// Bounded Model Checking Utils for Java

#ifndef CPROVER_JAVA_BYTECODE_JAVA_BMC_UTIL_H
#define CPROVER_JAVA_BYTECODE_JAVA_BMC_UTIL_H

class abstract_goto_modelt;
class optionst;
class symex_bmct;

/// Registers Java-specific preprocessing handlers with goto-symex
void java_setup_symex(
  const optionst &options,
  abstract_goto_modelt &goto_model,
  symex_bmct &symex);

#endif // CPROVER_JAVA_BYTECODE_JAVA_BMC_UTIL_H
