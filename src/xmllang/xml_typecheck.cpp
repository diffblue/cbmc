/*******************************************************************\

Module: SpecC Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <expr_util.h>
#include <arith_tools.h>
#include <i2string.h>

#include "xml_typecheck.h"
//#include "expr2xml.h"

/*******************************************************************\

Function: xml_typecheckt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string xml_typecheckt::to_string(const exprt &expr)
{
  std::string result;
  //expr2xml(expr, result);
  return result;
}

/*******************************************************************\

Function: xml_typecheckt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string xml_typecheckt::to_string(const typet &type)
{
  std::string result;
  //type2xml(type, result);
  return result;
}

/*******************************************************************\

Function: xml_typecheckt::convert_xmi

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void xml_typecheckt::convert_xmi(const xmlt &xml)
{
  const xmlt &content=get(xml, "XMI.content");

  for(xmlt::elementst::const_iterator
      c_it=content.elements.begin();
      c_it!=content.elements.end();
      c_it++)
    if(c_it->name=="Model_Management.Model")
      xml_typecheckt::convert_xmi_Model(*c_it);
}

/*******************************************************************\

Function: xml_typecheckt::convert_xmi_Model

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void xml_typecheckt::convert_xmi_Model(const xmlt &xml)
{
  const xmlt &Ns=
    get(xml, "Foundation.Core.Namespace.ownedElement");

  for(xmlt::elementst::const_iterator
      n_it=Ns.elements.begin();
      n_it!=Ns.elements.end();
      n_it++)
  {
    if(n_it->name=="Foundation.Core.Class")
      convert_xmi_class(*n_it);
    else if(n_it->name=="Foundation.Core.DataType")
      convert_xmi_DataType(*n_it);
    else
      throw "unexpected XMI: "+n_it->name;
  }
}

/*******************************************************************\

Function: xml_typecheckt::convert_xmi_class

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void xml_typecheckt::convert_xmi_class(const xmlt &xml)
{
  const xmlt &class_name=
    get(xml, "Foundation.Core.ModelElement.name");

  const xmlt &Ns=
    get(xml, "Foundation.Core.Namespace.ownedElement");

  symbolt symbol;

  symbol.base_name=class_name.data;
  symbol.name="xml::xmi::class::"+id2string(symbol.base_name);
  symbol.type=typet("class");

  for(xmlt::elementst::const_iterator
      n_it=Ns.elements.begin();
      n_it!=Ns.elements.end();
      n_it++)
  {
    if(n_it->name=="Behavioral_Elements.State_Machines.StateMachine")
    {
      symbol.value.copy_to_operands(exprt());     
      convert_xmi_StateMachine(*n_it, symbol.value.operands().back());
    }
    else
      throw "unexpected XMI: "+n_it->name;
  }

  if(symbol_table.move(symbol))
  {
    str << "class already in symbol table: " << symbol.name;
    throw 0;
  }
}

/*******************************************************************\

Function: xml_typecheckt::convert_xmi_DataType

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void xml_typecheckt::convert_xmi_DataType(const xmlt &xml)
{
  const xmlt &type_name=
    get(xml, "Foundation.Core.ModelElement.name");

  symbolt symbol;

  symbol.base_name=type_name.data;
  symbol.name="xml::xmi::DataType::"+id2string(symbol.base_name);
  symbol.is_type=true;
  symbol.type.make_nil();

  if(symbol_table.move(symbol))
  {
    str << "type already in symbol table: "
        << symbol.name;
    throw 0;
  }
}

/*******************************************************************\

Function: xml_typecheckt::convert_xmi_StateMachine

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void xml_typecheckt::convert_xmi_StateMachine(
  const xmlt &xml,
  exprt &dest)
{
  dest=exprt("StateMachine");

//  const xmlt &top=
//    get(xml, "Behavioral_Elements.State_Machines.StateMachine.top");

//  const xmlt &transitions=
//    get(xml, "Behavioral_Elements.State_Machines.StateMachine.transitions");


}

/*******************************************************************\

Function: xml_typecheckt::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void xml_typecheckt::typecheck()
{
  // see what we have

  const xmlt &element=xml_parse_tree.element;

  if(element.name=="XMI")
    convert_xmi(element);
  else
  {
    str << "I do not know how to handle "
        << element.name << std::endl;
    throw 0;
  }
}

/*******************************************************************\

Function: xml_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool xml_typecheck(
  xml_parse_treet &xml_parse_tree,
  symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  xml_typecheckt xml_typecheck(
    xml_parse_tree, symbol_table, module, message_handler);
  return xml_typecheck.typecheck_main();
}

/*******************************************************************\

Function: xml_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool xml_typecheck(exprt &expr,
                   std::ostream &err,
                   const namespacet &ns)
{
  symbol_tablet symbol_table;
  xml_parse_treet xml_parse_tree;

  #if 0
  bool result=false;

  xml_typecheckt xml_typecheck(xml_parse, symbol_table,
                                   ns.get_symbol_table(), "", err);

  try
  {
    xml_typecheck.typecheck_expr(expr);
  }

  catch(int e)
  {
    result=true;
  }

  catch(const char *e)
  {
    str << e << std::endl;
    result=true;
  }

  catch(const std::string &e)
  {
    str << e << std::endl;
    result=true;
  }

  return result;
  #endif
  return true;
}
