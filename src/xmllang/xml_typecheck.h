/*******************************************************************\

Module: SpecC Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_XML_TYPECHECK_H
#define CPROVER_XML_TYPECHECK_H

#include <util/typecheck.h>
#include <util/symbol_table.h>
#include <util/namespace.h>

#include "xml_parse_tree.h"

bool xml_typecheck(
  xml_parse_treet &xml_parse_tree,
  symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler);

bool xml_typecheck(
  exprt &expr,
  std::ostream &err,
  const namespacet &ns);

class xml_typecheckt:public typecheckt
{
public:
  xml_typecheckt(
    xml_parse_treet &_xml_parse_tree,
    symbol_tablet &_symbol_table,
    const std::string &_module,
    message_handlert &_message_handler):
    typecheckt(_message_handler),
    xml_parse_tree(_xml_parse_tree),
    symbol_table(_symbol_table)
  {
  }

  virtual ~xml_typecheckt() { }

  virtual void typecheck();

  // overload to use XML syntax
  
  virtual std::string to_string(const typet &type);
  virtual std::string to_string(const exprt &expr);

  // expressions
  void typecheck_expr(exprt &expr);
  
protected:
  xml_parse_treet &xml_parse_tree;
  symbol_tablet &symbol_table;
  
  void convert_xmi(const xmlt &xml);
  void convert_xmi_Model(const xmlt &xml);
  void convert_xmi_class(const xmlt &xml);
  void convert_xmi_DataType(const xmlt &xml);
  void convert_xmi_StateMachine(const xmlt &xml, exprt &dest);
  
  const xmlt &get(const xmlt &xml, const std::string &name)
  {
    xmlt::elementst::const_iterator it=xml.find(name);
    if(it==xml.elements.end())
      throw "failed to find "+name;
    return *it;
  }
};

#endif
