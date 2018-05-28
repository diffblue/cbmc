/*******************************************************************\

Module: Find Type Conversions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Find Type Conversions

#ifndef CPROVER_GOTO_ANALYZER_FIND_CONVERSION_H
#define CPROVER_GOTO_ANALYZER_FIND_CONVERSION_H

#include <unordered_set>

#include <util/irep.h>

class goto_modelt;

/// returns 'true' if a conversion is found
bool find_conversion(
  const goto_modelt &,
  const std::unordered_set<irep_idt> &conversions);

#endif // CPROVER_GOTO_ANALYZER_FIND_CONVERSION_H
