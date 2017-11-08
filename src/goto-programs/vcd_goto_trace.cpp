/*******************************************************************\

Module: Traces of GOTO Programs in VCD (Value Change Dump) Format

Author: Daniel Kroening

Date: June 2011

\*******************************************************************/

/// \file
/// Traces of GOTO Programs in VCD (Value Change Dump) Format

#include "vcd_goto_trace.h"

#include <ctime>
#include <ostream>
#include <cassert>

#include <util/arith_tools.h>
#include <util/pointer_offset_size.h>
#include <util/numbering.h>

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
    assert(expr.operands().size()==1);
    return as_vcd_binary(expr.op0(), ns);
  }

  // build "xxx"

  mp_integer width;

  if(type.id()==ID_unsignedbv ||
     type.id()==ID_signedbv ||
     type.id()==ID_floatbv ||
     type.id()==ID_fixedbv ||
     type.id()==ID_pointer ||
     type.id()==ID_bv)
    width=string2integer(type.get_string(ID_width));
  else
    width=pointer_offset_size(type, ns)*8;

  if(width>=0)
    return std::string(integer2size_t(width), 'x');

  return "";
}

namespace
{
class output_vcd_visitort final : public const_defaulted_visitor_generatort<
                                    const goto_trace_stept &,
                                    detail::trace_step_const_ref_typest>
{
public:
  output_vcd_visitort(
    const namespacet &ns,
    std::ostream &out,
    numbering<irep_idt> &n,
    unsigned &timestamp)
    : ns_{ns}, out_{out}, numbering_{n}, timestamp_{timestamp}
  {
  }

  void visit(const goto_trace_stept &) const override
  {
    // Do nothing
  }

  void visit(const trace_assignmentt &step) const override
  {
    irep_idt identifier = step.lhs_object.get_identifier();
    const typet &type = step.lhs_object.type();

    out_ << '#' << timestamp_ << "\n";
    timestamp_++;

    const auto number = numbering_.number(identifier);

    // booleans are special in VCD
    if(type.id() == ID_bool)
    {
      if(step.lhs_object_value.is_true())
        out_ << "1"
             << "V" << number << "\n";
      else if(step.lhs_object_value.is_false())
        out_ << "0"
             << "V" << number << "\n";
      else
        out_ << "x"
             << "V" << number << "\n";
    }
    else
    {
      std::string binary = as_vcd_binary(step.lhs_object_value, ns_);

      if(binary != "")
        out_ << "b" << binary << " V" << number << " "
             << "\n";
    }
  }

private:
  const namespacet &ns_;
  std::ostream &out_;
  numbering<irep_idt> &numbering_;
  unsigned &timestamp_;
};

} // namespace

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
    if(step->is_assignment())
    {
      irep_idt identifier=step->lhs_object.get_identifier();
      const typet &type=step->lhs_object.type();

      const auto number=n.number(identifier);

      mp_integer width;

      if(type.id()==ID_bool)
        width=1;
      else
        width=pointer_offset_bits(type, ns);

      if(width>=1)
        out << "$var reg " << width << " V" << number << " "
            << identifier << " $end" << "\n";
    }
  }

  // end of header
  out << "$enddefinitions $end" << "\n";

  unsigned timestamp = 0;

  for(const auto &step : goto_trace.steps)
  {
    step->accept(output_vcd_visitort{ns, out, n, timestamp});
  }
}
