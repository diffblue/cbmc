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
        it=parameters.begin();
        it!=parameters.end();
        it++)
    {
      if(it!=parameters.begin())
        out << ", ";
      output_type(it->type(), out);
    }
    
    out << ")";
    out << std::endl;
    out << "  {" << std::endl;

    for(instructionst::const_iterator
        it=instructions.begin();
        it!=instructions.end();
        it++)
    {
      if(it->location.get_line()!=irep_idt())
        out << "    // " << it->location << std::endl;

      out << "    " << it->address << ": " << it->statement;
      if(it->argument!=irep_idt()) out << " " << it->argument;
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
