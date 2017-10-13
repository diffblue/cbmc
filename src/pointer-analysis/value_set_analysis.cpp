/*******************************************************************\

Module: Value Set Propagation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Value Set Propagation

#include "value_set_analysis.h"

#include <util/prefix.h>
#include <util/cprover_prefix.h>

#include <langapi/language_util.h>

void convert(
  const goto_functionst &goto_functions,
  const value_set_analysist &value_set_analysis,
  xmlt &dest)
{
  dest=xmlt("value_set_analysis");

  for(goto_functionst::function_mapt::const_iterator
      f_it=goto_functions.function_map.begin();
      f_it!=goto_functions.function_map.end();
      f_it++)
  {
    xmlt &f=dest.new_element("function");
    f.new_element("identifier").data=id2string(f_it->first);
    value_set_analysis.convert(f_it->second.body, f_it->first, f);
  }
}

void convert(
  const goto_programt &goto_program,
  const value_set_analysist &value_set_analysis,
  xmlt &dest)
{
  dest=xmlt("value_set_analysis");

  value_set_analysis.convert(
    goto_program,
    "",
    dest.new_element("program"));
}
