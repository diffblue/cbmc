/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include "java_bytecode_parse_tree.h"

/*******************************************************************\

Function: java_bytecode_parse_treet::swap

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parse_treet::swap(
  java_bytecode_parse_treet &java_bytecode_parse_tree)
{
  java_bytecode_parse_tree.classes.swap(classes);
}

/*******************************************************************\

Function: java_bytecode_parse_treet::clear

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parse_treet::clear()
{
  classes.clear();
}

/*******************************************************************\

Function: java_bytecode_parse_treet::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parse_treet::output(std::ostream &out) const
{
  for(classest::const_iterator
      it=classes.begin();
      it!=classes.end();
      it++)
  {
    it->output(out);
  }
}

/*******************************************************************\

Function: java_bytecode_parse_treet::classt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parse_treet::classt::output(std::ostream &out) const
{
  out << "class " << name << " {" << "\n";

  for(memberst::const_iterator
      it=members.begin();
      it!=members.end();
      it++)
  {
    it->output(out);
  }
  
  out << "}" << "\n";
  out << "\n";
}

/*******************************************************************\

Function: java_bytecode_parse_treet::membert::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parse_treet::membert::output(std::ostream &out) const
{
  out << "  ";

  if(is_static)
    out << "static ";
  
  if(is_native)
    out << "native ";
  
  out << name;

  if(is_method)
  {
    out << "\n";

    out << "  {" << "\n";

    for(instructionst::const_iterator
        i_it=instructions.begin();
        i_it!=instructions.end();
        i_it++)
    {
      if(i_it->source_location.get_line()!=irep_idt())
        out << "    // " << i_it->source_location << "\n";

      out << "    " << i_it->address << ": ";
      out << i_it->statement;
      
      for(std::vector<exprt>::const_iterator
          a_it=i_it->args.begin(); a_it!=i_it->args.end(); a_it++)
      {
        if(a_it!=i_it->args.begin()) out << ",";
        out << " " << *a_it;
      }

      out << "\n";
    }

    out << "  }" << "\n";
  }
  else
  {
    out << ";";
  }

  out << "\n";
}
