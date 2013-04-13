/*******************************************************************\

Module: Function Call Graphs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>
#include <util/xml.h>

#include "call_graph.h"

/*******************************************************************\

Function: call_grapht::call_grapht

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

call_grapht::call_grapht()
{
}

/*******************************************************************\

Function: call_grapht::call_grapht

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

call_grapht::call_grapht(const goto_functionst &goto_functions)
{
  forall_goto_functions(f_it, goto_functions)
  {
    const goto_programt &body=f_it->second.body;
    add(f_it->first, body);
  }
}

/*******************************************************************\

Function: call_grapht::add

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void call_grapht::add(
  const irep_idt &function,
  const goto_programt &body)
{
  forall_goto_program_instructions(i_it, body)
  {
    if(i_it->is_function_call())
    {
      const exprt &function_expr=to_code_function_call(i_it->code).function();
      if(function_expr.id()==ID_symbol)
        add(function, to_symbol_expr(function_expr).get_identifier());
    }
  }
}

/*******************************************************************\

Function: call_grapht::add

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void call_grapht::add(
  const irep_idt &caller,
  const irep_idt &callee)
{
  graph.insert(std::pair<irep_idt, irep_idt>(caller, callee));
}

/*******************************************************************\

Function: call_grapht::output_dot

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void call_grapht::output_dot(std::ostream &out) const
{
  out << "digraph call_graph {" << std::endl;

  for(grapht::const_iterator it=graph.begin();
      it!=graph.end();
      it++)
  {
    out << "  \"" << it->first << "\" -> "
        << "\"" << it->second << "\" "
        << " [arrowhead=\"vee\"];"
        << std::endl;
  }
  
  out << "}" << std::endl;
}

/*******************************************************************\

Function: call_grapht::output

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void call_grapht::output(std::ostream &out) const
{
  for(grapht::const_iterator
      it=graph.begin();
      it!=graph.end();
      it++)
  {
    out << it->first << " -> " << it->second << std::endl;
  }
}

/*******************************************************************\

Function: call_grapht::output_xml

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void call_grapht::output_xml(std::ostream &out) const
{
  for(grapht::const_iterator
      it=graph.begin();
      it!=graph.end();
      it++)
  {
    out << "<call_graph_edge caller=\"";
    xmlt::escape_attribute(id2string(it->first), out);
    out << "\" callee=\"";
    xmlt::escape_attribute(id2string(it->second), out);
    out << "\">" << std::endl;
  }
}
