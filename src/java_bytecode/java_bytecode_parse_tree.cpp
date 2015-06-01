/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include <langapi/language_util.h>

#include "java_bytecode_parse_tree.h"

/*******************************************************************\

Function: java_bytecode_parse_treet::swap

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parse_treet::classt::swap(
  classt &other)
{
  other.name.swap(name);
  other.extends.swap(extends);
  std::swap(other.is_abstract, is_abstract);
  other.implements.swap(implements);
  other.fields.swap(fields);
  other.methods.swap(methods);
}

/*******************************************************************\

Function: java_bytecode_parse_treet::classt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parse_treet::output(std::ostream &out) const
{
  parsed_class.output(out);

  out << "Class references:\n";
  for(class_refst::const_iterator it=class_refs.begin();
      it!=class_refs.end();
      it++)
  {
    out << "  " << *it << '\n';
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
  out << "class " << name;
  if(!extends.empty()) out << " extends " << extends;
  out << " {" << '\n';

  for(fieldst::const_iterator
      it=fields.begin();
      it!=fields.end();
      it++)
  {
    it->output(out);
  }
  
  out << '\n';
  
  for(methodst::const_iterator
      it=methods.begin();
      it!=methods.end();
      it++)
  {
    it->output(out);
  }
  
  out << '}' << '\n';
  out << '\n';
  
}

/*******************************************************************\

Function: java_bytecode_parse_treet::methodt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parse_treet::methodt::output(std::ostream &out) const
{
  out << "  ";

  if(is_public)
    out << "public ";
  
  if(is_static)
    out << "static ";
  
  if(is_native)
    out << "native ";
  
  out << name;
  out << " : " << signature;

  out << '\n';

  out << "  {" << '\n';

  for(instructionst::const_iterator
      i_it=instructions.begin();
      i_it!=instructions.end();
      i_it++)
  {
    if(i_it->source_location.get_line()!=irep_idt())
      out << "    // " << i_it->source_location << '\n';

    out << "    " << i_it->address << ": ";
    out << i_it->statement;
    
    for(std::vector<exprt>::const_iterator
        a_it=i_it->args.begin(); a_it!=i_it->args.end(); a_it++)
    {
      if(a_it!=i_it->args.begin()) out << ',';
      #if 0
      out << ' ' << from_expr(*a_it);
      #else
      out << ' ' << *a_it;
      #endif
    }

    out << '\n';
  }

  out << "  }" << '\n';

  out << '\n';
}

/*******************************************************************\

Function: java_bytecode_parse_treet::fieldt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parse_treet::fieldt::output(std::ostream &out) const
{
  out << "  ";

  if(is_public)
    out << "public ";
  
  if(is_static)
    out << "static ";
  
  out << name;
  out << " : " << signature << ';';

  out << '\n';
}

