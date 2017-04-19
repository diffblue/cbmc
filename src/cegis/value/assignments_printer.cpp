/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/namespace.h>
#include <ansi-c/expr2c.h>

#include <cegis/value/assignments_printer.h>

void print_assignments(messaget::mstreamt &os, const symbol_tablet &st,
    const std::map<const irep_idt, exprt> &assignments)
{
  const namespacet ns(st);
  for(const std::map<const irep_idt, exprt>::value_type &assignment : assignments)
  {
    os << "<assignment>" << messaget::endl;
    os << "  <id>" << assignment.first << "</id>" << messaget::endl;
    os << "  <value>" << expr2c(assignment.second, ns) << "</value>" << messaget::endl;
    os << "</assignment>" << messaget::endl;
  }
  os << messaget::eom;
}
