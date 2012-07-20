/*******************************************************************\

Module: Expressions in XML

Author: Daniel Kroening

  Date: November 2005

\*******************************************************************/

#include "namespace.h"
#include "expr.h"
#include "xml.h"
#include "arith_tools.h"
#include "ieee_float.h"
#include "fixedbv.h"
#include "std_expr.h"

#include "xml_expr.h"

/*******************************************************************\

Function: xml

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

xmlt xml(const locationt &location)
{
  xmlt result;

  result.name="location";
  
  // these will go away
  result.new_element("file").data=id2string(location.get_file());
  result.new_element("line").data=id2string(location.get_line());
  result.new_element("function").data=id2string(location.get_function());
  
  // these are to stay
  if(location.get_file()!="")
    result.set_attribute("file", id2string(location.get_file()));

  if(location.get_line()!="")
    result.set_attribute("line", id2string(location.get_line()));

  if(location.get_function()!="")
    result.set_attribute("function", id2string(location.get_function()));
  
  return result;
}

/*******************************************************************\

Function: xml

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

xmlt xml(
  const exprt &expr,
  const namespacet &ns)
{
  const typet &type=ns.follow(expr.type());
  xmlt result;
  
  if(expr.id()==ID_constant)
  {
    if(type.id()==ID_unsignedbv ||
       type.id()==ID_signedbv)
    {
      result.name="integer";
      result.set_attribute("binary", expr.get_string(ID_value));

      mp_integer i;
      if(!to_integer(expr, i))
        result.data=integer2string(i);
    }
    else if(type.id()==ID_bv)
    {
      result.name="bitvector";
      result.set_attribute("binary", expr.get_string(ID_value));
      result.data=expr.get_string(ID_value);
    }
    else if(type.id()==ID_fixedbv)
    {
      result.name="fixed";
      result.set_attribute("binary", expr.get_string(ID_value));
      result.data=fixedbvt(to_constant_expr(expr)).to_ansi_c_string();
    }
    else if(type.id()==ID_floatbv)
    {
      result.name="float";
      result.set_attribute("binary", expr.get_string(ID_value));
      result.data=ieee_floatt(to_constant_expr(expr)).to_ansi_c_string();
    }
    else if(type.id()==ID_pointer)
    {
      result.name="pointer";
      result.set_attribute("binary", expr.get_string(ID_value));
      if(expr.get(ID_value)==ID_NULL)
        result.data="NULL";
    }
    else if(type.id()==ID_bool)
    {
      result.name="boolean";
      result.set_attribute("binary", expr.is_true()?"1":"0");
      result.data=expr.is_true()?"TRUE":"FALSE";
    }
    else
    {
      result.name="unknown";
    }
  }
  else if(expr.id()==ID_array)
  {
    result.name="array";
    
    unsigned index=0;
    
    forall_operands(it, expr)
    {
      xmlt &e=result.new_element("element");
      e.set_attribute("index", index);
      e.new_element(xml(*it, ns));
      index++;
    }
  }
  else if(expr.id()==ID_struct)
  {
    result.name="struct";
  
    forall_operands(it, expr)
    {
      xmlt &e=result.new_element("member");
      e.new_element(xml(*it, ns));
    }
  }
  else if(expr.id()==ID_union)
  { 
    result.name="union";
    
    assert(expr.operands().size()==1);
    
    xmlt &e=result.new_element("member");
    e.new_element(xml(expr.op0(), ns));
  }
  else
    result.name="unknown";

  return result;
}

