/*******************************************************************\

Module: Find Type Conversions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "find_conversion.h"

#include <util/cprover_prefix.h>

#include <ansi-c/expr2c.h>

#include <goto-programs/goto_model.h>

#include <iostream>

class find_conversiont
{
public:
  find_conversiont(
    const std::unordered_set<irep_idt> &_conversions,
    const namespacet &_ns):
    conversions(_conversions),
    ns(_ns)
  {
  }

  bool operator()(
    const typet &from_type,
    const typet &to_type,
    const source_locationt &);

  bool operator()(const exprt &);
  bool operator()(const goto_programt::instructiont &);
  bool operator()(const goto_programt &);
  bool operator()(const goto_functiont &);
  bool operator()(const goto_functionst &);

protected:
  const std::unordered_set<irep_idt> &conversions;
  const namespacet &ns;
};

bool find_conversiont::operator()(
  const typet &from_type, const typet &to_type,
  const source_locationt &loc)
{
  bool found=false;

  irep_idt from_typedef=from_type.get(ID_C_typedef);
  irep_idt to_typedef=to_type.get(ID_C_typedef);

  if(from_typedef!=to_typedef)
  {
    if(conversions.find(from_typedef)!=conversions.end())
    {
      std::cout
        << loc
        << ": conversion from "
        << from_typedef
        << " to "
        << type2c(to_type, ns)
        << '\n';
      found=true;
    }

    if(conversions.find(to_typedef)!=conversions.end())
    {
      std::cout
        << loc
        << ": conversion to "
        << to_typedef
        << " from "
        << type2c(from_type, ns)
        << '\n';
      found=true;
    }
  }

  return found;
}

bool find_conversiont::operator()(const exprt &expr)
{
  bool found=false;

  // recursion
  for(const auto & op : expr.operands())
    if(operator()(op))
      found=true;

  if(expr.id()==ID_equal ||
     expr.id()==ID_notequal ||
     expr.id()==ID_lt ||
     expr.id()==ID_gt ||
     expr.id()==ID_le ||
     expr.id()==ID_ge)
  {
    if(expr.operands().size()==2)
    {
      if(operator()(expr.op0().type(), expr.op1().type(), expr.find_source_location()))
      {
        std::cout << "In: " << expr2c(expr, ns) << '\n';
        found=true;
      }
    }
  }
  else if(expr.id()==ID_address_of)
  {
  }
  else if(expr.id()==ID_index)
  {
  }
  else if(expr.id()==ID_dereference)
  {
  }
  else
  {
    for(const auto & op : expr.operands())
    {
      if(operator()(op.type(), expr.type(), expr.find_source_location()))
      {
        std::cout << "In: " << expr2c(expr, ns) << '\n';
        found=true;
      }
    }
  }

  return found;
}

bool find_conversiont::operator()(
  const goto_programt::instructiont &instruction)
{
  bool found=false;

  switch(instruction.type)
  {
  case GOTO:
    if(operator()(instruction.guard))
      found=true;
    break;
  
  case ASSIGN:
    if(operator()(instruction.code))
      found=true;
    break;

  case FUNCTION_CALL:
    {
      const auto &fc=to_code_function_call(instruction.code);
      const auto &code_type=to_code_type(fc.function().type());
      const auto &parameters=code_type.parameters();
      const auto &arguments=fc.arguments();
      const auto &lhs=fc.lhs();

      for(std::size_t i=0; i<arguments.size(); i++)
      {
        auto from=arguments[i].type();
        typet to;

        if(i<parameters.size())
          to=parameters[i].type();
        else
          to=empty_typet();

        if(operator()(from, to, arguments[i].find_source_location()))
        {
          std::cout << "In: " << expr2c(fc, ns) << '\n';
          found=true;
        }
      }

      if(lhs.is_not_nil())
      {
        if(operator()(lhs.type(), code_type.return_type(), lhs.find_source_location()))
        {
          std::cout << "In: " << expr2c(fc, ns) << '\n';
          found=true;
        }
      }
    }
    break;
  
  default:;
  }

  return found;
}

bool find_conversiont::operator()(
  const goto_programt &goto_program)
{
  bool found=false;

  for(const auto & i : goto_program.instructions)
    if(operator()(i))
      found=true;

  return found;
}

bool find_conversiont::operator()(const goto_functionst &goto_functions)
{
  bool found=false;

  for(const auto &function : goto_functions.function_map)
    if(function.first != CPROVER_PREFIX "initialize" &&
       function.first != CPROVER_PREFIX "start")
      if(operator()(function.second.body))
        found=true;

  return found;
}

bool find_conversion(
  const goto_modelt &goto_model,
  const std::unordered_set<irep_idt> &conversions)
{
  const namespacet ns(goto_model.symbol_table);
  return find_conversiont(conversions, ns)(goto_model.goto_functions);
}
