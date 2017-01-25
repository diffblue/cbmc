/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <ansi-c/expr2c.h>
#include <util/namespace.h>

#include <cegis/control/learn/print_control_solution.h>

void print_control_array(messaget::mstreamt &os, const array_exprt &array,
    const char * name, const symbol_tablet &st)
{
  const namespacet ns(st);
  const array_exprt::operandst &ops=array.operands();
  os << '<' << name << '>' << messaget::endl;
  for (const array_exprt::operandst::value_type &value : ops)
    os << "<item>" << expr2c(value, ns) << "</item>" << messaget::endl;
  os << "</" << name << '>' << messaget::endl;
  os << '<' << name << "_size>" << ops.size();
  os << "</" << name << "_size>" << messaget::endl;
}
