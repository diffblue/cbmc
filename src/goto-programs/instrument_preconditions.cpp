/*******************************************************************\

Module: Move preconditions of a function
        to the call-site of the function

Author: Daniel Kroening

Date:   September 2017

\*******************************************************************/

#include "instrument_preconditions.h"

#include <util/replace_symbol.h>

std::vector<goto_programt::const_targett> get_preconditions(
  const symbol_exprt &function,
  const goto_functionst &goto_functions)
{
  const irep_idt &identifier=function.get_identifier();

  auto f_it=goto_functions.function_map.find(identifier);
  if(f_it==goto_functions.function_map.end())
    return {};

  const auto &body=f_it->second.body;

  std::vector<goto_programt::const_targett> result;

  for(auto i_it=body.instructions.begin();
      i_it!=body.instructions.end();
      i_it++)
  {
    if(i_it->is_location() ||
       i_it->is_skip())
      continue; // ignore

    if(i_it->is_assert() &&
       i_it->source_location.get_property_class()==ID_precondition)
      result.push_back(i_it);
    else
      break; // preconditions must be at the front
  }

  return result;
}

void remove_preconditions(goto_programt &goto_program)
{
  for(auto &instruction : goto_program.instructions)
  {
    if(instruction.is_location() ||
       instruction.is_skip())
      continue; // ignore

    if(instruction.is_assert() &&
       instruction.source_location.get_property_class()==ID_precondition)
      instruction.type=LOCATION;
    else
      break; // preconditions must be at the front
  }
}

replace_symbolt actuals_replace_map(
  const code_function_callt &call,
  const namespacet &ns)
{
  PRECONDITION(call.function().id()==ID_symbol);
  const symbolt &s=ns.lookup(to_symbol_expr(call.function()));
  const auto &code_type=to_code_type(s.type);
  const auto &parameters=code_type.parameters();
  const auto &arguments=call.arguments();

  replace_symbolt result;
  std::size_t count=0;
  for(const auto &p : parameters)
  {
    if(p.get_identifier()!=irep_idt() &&
       arguments.size()>count)
    {
      const exprt a =
        typecast_exprt::conditional_cast(arguments[count], p.type());
      result.insert(symbol_exprt(p.get_identifier(), p.type()), a);
    }
    count++;
  }

  return result;
}

void instrument_preconditions(
  const goto_modelt &goto_model,
  goto_programt &goto_program)
{
  const namespacet ns(goto_model.symbol_table);

  for(auto it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++)
  {
    if(it->is_function_call())
    {
      // does the function we call have preconditions?
      const auto &call = it->get_function_call();

      if(call.function().id()==ID_symbol)
      {
        auto preconditions=
          get_preconditions(to_symbol_expr(call.function()),
                            goto_model.goto_functions);

        source_locationt source_location=it->source_location;
        irep_idt function=it->function;

        replace_symbolt r=actuals_replace_map(call, ns);

        // add before the call, with location of the call
        for(const auto &p : preconditions)
        {
          goto_program.insert_before_swap(it);
          exprt instance=p->guard;
          r(instance);
          it->make_assertion(instance);
          it->function=function;
          it->source_location=source_location;
          it->source_location.set_property_class(ID_precondition_instance);
          it->source_location.set_comment(p->source_location.get_comment());
          it++;
        }
      }
    }
  }
}

void instrument_preconditions(goto_modelt &goto_model)
{
  // add at call site
  for(auto &f_it : goto_model.goto_functions.function_map)
    instrument_preconditions(
      goto_model,
      f_it.second.body);

  // now remove the preconditions
  for(auto &f_it : goto_model.goto_functions.function_map)
    remove_preconditions(f_it.second.body);
}

void remove_preconditions(goto_functiont &goto_function)
{
  remove_preconditions(goto_function.body);
}

void remove_preconditions(goto_modelt &goto_model)
{
  for(auto &f_it : goto_model.goto_functions.function_map)
    remove_preconditions(f_it.second);
}
