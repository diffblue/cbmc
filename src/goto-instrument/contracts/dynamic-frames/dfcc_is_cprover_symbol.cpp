/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmasrd@amazon.com

Date: March 2023

\*******************************************************************/

#include "dfcc_is_cprover_symbol.h"

#include <util/cprover_prefix.h>
#include <util/prefix.h>
#include <util/suffix.h>

bool dfcc_is_cprover_symbol(const irep_idt &id)
{
  std::string str = id2string(id);
  return has_prefix(str, CPROVER_PREFIX) || has_prefix(str, "__VERIFIER") ||
         has_prefix(str, "nondet") || has_suffix(str, "$object");
}
