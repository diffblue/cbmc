/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_bytecode_parse_tree.h"

/*******************************************************************\

Function: java_bytecode_parse_treet::swap

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parse_treet::swap(java_bytecode_parse_treet &java_bytecode_parse_tree)
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
  out << "class " << name << " {" << std::endl;

  for(memberst::const_iterator
      it=members.begin();
      it!=members.end();
      it++)
  {
    it->output(out);
  }
  
  out << "}" << std::endl;
  out << std::endl;
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
  if(type.id()!=irep_idt())
  {
    output_type(type, out);
    out << " ";
  }
  
  out << name;

  if(method)
  {
    out << "(";
    for(code_typet::parameterst::const_iterator
        p_it=parameters.begin();
        p_it!=parameters.end();
        p_it++)
    {
      if(p_it!=parameters.begin())
        out << ", ";
      output_type(p_it->type(), out);
    }
    
    out << ")";
    out << std::endl;
    out << "  {" << std::endl;

    for(instructionst::const_iterator
        i_it=instructions.begin();
        i_it!=instructions.end();
        i_it++)
    {
      if(i_it->location.get_line()!=irep_idt())
        out << "    // " << i_it->location << std::endl;

      out << "    " << i_it->address << ": " << i_it->statement;
      
      for(std::vector<exprt>::const_iterator
          a_it=i_it->args.begin(); a_it!=i_it->args.end(); a_it++)
      {
        if(a_it!=i_it->args.begin()) out << ", ";
        out << *a_it;
      }

      out << std::endl;
    }

    out << "  }" << std::endl;
  }
  else
    out << ";" << std::endl;

  out << std::endl;
}

/*******************************************************************\

Function: java_bytecode_parse_treet::output_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parse_treet::output_type(
  const typet &type,
  std::ostream &out)
{
  if(type.id()==ID_array)
  {
    output_type(type.subtype(), out);
    out << "[]";
  }
  else if(type.id()==ID_symbol)
  {
    out << type.get(ID_identifier);
  }
  else
    out << type.id();
}
