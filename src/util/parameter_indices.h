/*******************************************************************\

Module: Parameter indexing

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Parameter indexing

#ifndef CPROVER_UTIL_PARAMETER_INDICES_H
#define CPROVER_UTIL_PARAMETER_INDICES_H

#include <unordered_map>
#include "std_types.h"

std::map<irep_idt, std::size_t>
  get_parameter_indices(const code_typet &fn_type);

#endif
