/*******************************************************************\

Module: Value Set Propagation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Value Set Propagation

#include "value_set_analysis.h"

#include <util/cprover_prefix.h>
#include <util/prefix.h>
#include <util/xml_irep.h>

#include <langapi/language_util.h>

void value_sets_to_xml(
  const std::function<const value_sett &(goto_programt::const_targett)>
    &get_value_set,
  const goto_programt &goto_program,
  xmlt &dest)
{
  source_locationt previous_location;

  forall_goto_program_instructions(i_it, goto_program)
  {
    const source_locationt &location=i_it->source_location;

    if(location==previous_location)
      continue;

    if(location.is_nil() || location.get_file().empty())
      continue;

    // find value set
    const value_sett &value_set=get_value_set(i_it);

    xmlt &i=dest.new_element("instruction");
    i.new_element()=::xml(location);

    for(value_sett::valuest::const_iterator
        v_it=value_set.values.begin();
        v_it!=value_set.values.end();
        v_it++)
    {
      xmlt &var=i.new_element("variable");
      var.new_element("identifier").data=
        id2string(v_it->first);

      #if 0
      const value_sett::expr_sett &expr_set=
        v_it->second.expr_set();

      for(value_sett::expr_sett::const_iterator
          e_it=expr_set.begin();
          e_it!=expr_set.end();
          e_it++)
      {
        std::string value_str=
          from_expr(ns, identifier, *e_it);

        var.new_element("value").data=
          xmlt::escape(value_str);
      }
      #endif
    }
  }
}

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
    value_set_analysis.convert(f_it->second.body, f);
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
    dest.new_element("program"));
}
