/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include <util/symbol_table.h>
#include <util/namespace.h>

#include <langapi/language_util.h>

#include "expr2java.h"

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
  other.annotations.swap(annotations);
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
  for(const auto & annotation : annotations)
  {
    annotation.output(out);
    out << '\n';
  }

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

Function: java_bytecode_parse_treet::annotationt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parse_treet::annotationt::output(std::ostream &out) const
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  out << '@' << type2java(type, ns);

  if(!element_value_pairs.empty())
  {
    out << '(';

    bool first=true;
    for(const auto & element_value_pair : element_value_pairs)
    {
      if(first) first=false; else out << ", ";
      element_value_pair.output(out);
    }

    out << ')';
  }
}

/*******************************************************************\

Function: java_bytecode_parse_treet::annotationt::element_value_pairt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parse_treet::annotationt::element_value_pairt::output(std::ostream &out) const
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  out << '"' << element_name << '"' << '=';
  out << expr2java(value, ns);
}

/*******************************************************************\

Function: java_bytecode_parse_treet::methodt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parse_treet::methodt::output(std::ostream &out) const
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  for(const auto & annotation : annotations)
  {
    out << "  ";
    annotation.output(out);
    out << '\n';
  }

  out << "  ";

  if(is_public)
    out << "public ";

  if(is_protected)
    out << "protected ";

  if(is_private)
    out << "private ";

  if(is_static)
    out << "static ";

  if(is_final)
    out << "final ";

  if(is_native)
    out << "native ";

  if(is_synchronized)
    out << "synchronized ";

  out << name;
  out << " : " << signature;

  out << '\n';

  out << "  {" << '\n';

  for(const auto & i : instructions)
  {
    if(i.source_location.get_line()!=irep_idt())
      out << "    // " << i.source_location << '\n';

    out << "    " << i.address << ": ";
    out << i.statement;

    for(std::vector<exprt>::const_iterator
        a_it=i.args.begin(); a_it!=i.args.end(); a_it++)
    {
      if(a_it!=i.args.begin()) out << ',';
      #if 0
      out << ' ' << from_expr(*a_it);
      #else
      out << ' ' << expr2java(*a_it, ns);
      #endif
    }

    out << '\n';
  }

  out << "  }" << '\n';

  out << '\n';

  out << "  Locals:\n";
  for(const auto & v : local_variable_table)
  {
    out << "    " << v.index << ": " << v.name << ' '
        << v.signature << '\n';
  }

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
  for(const auto & annotation : annotations)
  {
    out << "  ";
    annotation.output(out);
    out << '\n';
  }

  out << "  ";

  if(is_public)
    out << "public ";

  if(is_static)
    out << "static ";

  out << name;
  out << " : " << signature << ';';

  out << '\n';
}
