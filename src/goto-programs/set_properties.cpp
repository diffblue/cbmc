/*******************************************************************\

Module: Set Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Set Properties

#include "set_properties.h"

#include <util/exception_utils.h>

#include "goto_model.h"

#include <algorithm>
#include <unordered_set>

void set_properties(
  goto_programt &goto_program,
  std::unordered_set<irep_idt> &property_set)
{
  for(goto_programt::instructionst::iterator
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++)
  {
    if(!it->is_assert())
      continue;

    irep_idt property_id = it->source_location().get_property_id();

    std::unordered_set<irep_idt>::iterator c_it =
      property_set.find(property_id);

    if(c_it==property_set.end())
      it->turn_into_skip();
    else
      property_set.erase(c_it);
  }
}

void label_properties(goto_modelt &goto_model)
{
  label_properties(goto_model.goto_functions);
}

void label_properties(
  goto_programt &goto_program,
  std::map<irep_idt, std::size_t> &property_counters)
{
  for(goto_programt::instructionst::iterator
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++)
  {
    if(!it->is_assert())
      continue;

    irep_idt function = it->source_location().get_function();

    std::string prefix=id2string(function);
    if(!it->source_location().get_property_class().empty())
    {
      if(!prefix.empty())
        prefix+=".";

      std::string class_infix =
        id2string(it->source_location().get_property_class());

      // replace the spaces by underscores
      std::replace(class_infix.begin(), class_infix.end(), ' ', '_');

      prefix+=class_infix;
    }

    if(!prefix.empty())
      prefix+=".";

    std::size_t &count=property_counters[prefix];

    count++;

    std::string property_id=prefix+std::to_string(count);

    it->source_location_nonconst().set_property_id(property_id);
  }
}

void label_properties(goto_programt &goto_program)
{
  std::map<irep_idt, std::size_t> property_counters;
  label_properties(goto_program, property_counters);
}

void set_properties(
  goto_modelt &goto_model,
  const std::list<std::string> &properties)
{
  set_properties(goto_model.goto_functions, properties);
}

void set_properties(
  goto_functionst &goto_functions,
  const std::list<std::string> &properties)
{
  std::unordered_set<irep_idt> property_set;

  property_set.insert(properties.begin(), properties.end());

  for(auto &gf_entry : goto_functions.function_map)
    set_properties(gf_entry.second.body, property_set);

  if(!property_set.empty())
    throw invalid_command_line_argument_exceptiont(
      "property " + id2string(*property_set.begin()) + " unknown",
      "--property id");
}

void label_properties(goto_functionst &goto_functions)
{
  std::map<irep_idt, std::size_t> property_counters;

  for(goto_functionst::function_mapt::iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    label_properties(it->second.body, property_counters);
}
