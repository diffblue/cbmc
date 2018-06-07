/*******************************************************************\

Module: Traces of GOTO Programs in VCD (Value Change Dump) Format

Author: Daniel Kroening

Date: June 2011

\*******************************************************************/

/// \file
/// Traces of GOTO Programs in VCD (Value Change Dump) Format

#include "vcd_goto_trace.h"

#include <ctime>

#include <util/arith_tools.h>
#include <util/numbering.h>
#include <util/pointer_offset_size.h>

std::string as_vcd_binary(
  const exprt &expr,
  const namespacet &ns)
{
  const typet &type=ns.follow(expr.type());

  if(expr.id()==ID_constant)
  {
    if(type.id()==ID_unsignedbv ||
       type.id()==ID_signedbv ||
       type.id()==ID_bv ||
       type.id()==ID_fixedbv ||
       type.id()==ID_floatbv ||
       type.id()==ID_pointer)
      return expr.get_string(ID_value);
  }
  else if(expr.id()==ID_array)
  {
    std::string result;

    forall_operands(it, expr)
      result+=as_vcd_binary(*it, ns);

    return result;
  }
  else if(expr.id()==ID_struct)
  {
    std::string result;

    forall_operands(it, expr)
      result+=as_vcd_binary(*it, ns);

    return result;
  }
  else if(expr.id()==ID_union)
  {
    return as_vcd_binary(to_union_expr(expr).op(), ns);
  }

  // build "xxx"

  const auto width = pointer_offset_bits(type, ns);

  if(width.has_value())
    return std::string(numeric_cast_v<std::size_t>(*width), 'x');
  else
    return "";
}

void output_vcd(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  std::ostream &out)
{
  time_t t;
  time(&t);
  out << "$date\n  " << ctime(&t) << "$end" << "\n";

  // this is pretty arbitrary
  out << "$timescale 1 ns $end" << "\n";

  // we first collect all variables that are assigned

  numbering<irep_idt> n;

  for(const auto &step : goto_trace.steps)
  {
    if(step.is_assignment())
    {
      auto lhs_object=step.get_lhs_object();
      if(lhs_object.has_value())
      {
        irep_idt identifier=lhs_object->get_identifier();
        const typet &type=lhs_object->type();

        const auto number=n.number(identifier);

        const auto width = pointer_offset_bits(type, ns);

        if(width.has_value() && (*width) >= 1)
          out << "$var reg " << (*width) << " V" << number << " " << identifier
              << " $end"
              << "\n";
      }
    }
  }

  // end of header
  out << "$enddefinitions $end" << "\n";

  unsigned timestamp=0;

  for(const auto &step : goto_trace.steps)
  {
    switch(step.type)
    {
    case goto_trace_stept::typet::ASSIGNMENT:
      {
        auto lhs_object=step.get_lhs_object();
        if(lhs_object.has_value())
        {
          irep_idt identifier=lhs_object->get_identifier();
          const typet &type=lhs_object->type();

          out << '#' << timestamp << "\n";
          timestamp++;

          const auto number=n.number(identifier);

          // booleans are special in VCD
          if(type.id()==ID_bool)
          {
            if(step.full_lhs_value.is_true())
              out << "1" << "V" << number << "\n";
            else if(step.full_lhs_value.is_false())
              out << "0" << "V" << number << "\n";
            else
              out << "x" << "V" << number << "\n";
          }
          else
          {
            std::string binary=as_vcd_binary(step.full_lhs_value, ns);

            if(binary!="")
              out << "b" << binary << " V" << number << " " << "\n";
          }
        }
      }
      break;

    default:
      {
      }
    }
  }
}
