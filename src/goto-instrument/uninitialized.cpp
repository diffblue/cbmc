/*******************************************************************\

Module: Detection for Uninitialized Local Variables

Author: Daniel Kroening

Date: January 2010

\*******************************************************************/

/// \file
/// Detection for Uninitialized Local Variables

#include "uninitialized.h"

#include <goto-programs/goto_model.h>

#include <analyses/uninitialized_domain.h>

void show_uninitialized(
  const goto_modelt &goto_model,
  std::ostream &out)
{
  const namespacet ns(goto_model.symbol_table);

  for(const auto &gf_entry : goto_model.goto_functions.function_map)
  {
    if(gf_entry.second.body_available())
    {
      out << "////\n";
      out << "//// Function: " << gf_entry.first << '\n';
      out << "////\n\n";
      uninitialized_analysist uninitialized_analysis;
      uninitialized_analysis(gf_entry.first, gf_entry.second.body, ns);
      uninitialized_analysis.output(
        ns, gf_entry.first, gf_entry.second.body, out);
    }
  }
}
