/*******************************************************************\

Module: Value Set Propagation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/prefix.h>
#include <util/cprover_prefix.h>
#include <util/xml_expr.h>
#include <util/xml.h>
#include <util/simplify_expr.h>


#include <langapi/language_util.h>

#include "value_set_analysis.h"

#include "value_set_check.h"

// #define DEBUG

#ifdef DEBUG
#include <iostream>
#endif


/*******************************************************************\

Function: value_set_checkt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_checkt::operator()(
  const goto_functionst &goto_functions)
{
  for(goto_functionst::function_mapt::const_iterator
      f_it=goto_functions.function_map.begin();
      f_it!=goto_functions.function_map.end();
      f_it++)
  {
    if(f_it->second.body_available())
    {
      operator()(f_it->second.body);
    }
  }
}

bool value_set_checkt::is_null(const exprt &src)
{
  if(src.is_constant()
      && to_constant_expr(src).get_value()=="NULL")
    return true;

  if(src.id()==ID_object_descriptor && (src.op0()).id()=="NULL-object")
    return true;

  if(src.operands().size()==1)
    return is_null(src.op0());

  return false;
}


bool value_set_checkt::contains_null(const value_setst::valuest &values)
{
  for(value_setst::valuest::const_iterator
      it=values.begin();
      it!=values.end();
      ++it)
  {
    if(is_null(*it))
      return true;
  }

  return false;
}


bool value_set_checkt::contains_invalid(const value_setst::valuest &values)
{
  for(value_setst::valuest::const_iterator
      it=values.begin();
      it!=values.end();
      ++it)
  {
    if(it->id()=="ID_invalid")
      return true;
  }

  return false;
}

/*******************************************************************\

Function: value_set_checkt::eval_rec()

  Inputs:

 Outputs:

 Purpose: recursively evaluate a pointer expression

\*******************************************************************/

exprt value_set_checkt::eval_rec(
  const exprt &src,
  const value_sett &value_set,
  bool negated,
  bool &inconclusive)
{
  exprt result;

  if(src.id()==ID_equal)
  {
    const exprt &op0=src.op0();
    const exprt &op1=src.op1();
    
    if(op0.id()==ID_pointer_object
      && op1.id()==ID_pointer_object)
    {
      value_sett::object_mapt obj_map1;
      value_sett::object_mapt obj_map2;
      
      value_set.get_value_set(op0.op0(), obj_map1, ns, false);
      value_set.get_value_set(op1.op0(), obj_map2, ns, false);

      if(value_sett::overlap(obj_map1, obj_map2, inconclusive))
      {
	      result= negated ? (exprt) false_exprt() : (exprt) true_exprt();
      }
      else
      {
        result= negated ? (exprt) true_exprt() : (exprt) false_exprt();
      }
    }
    else
    {     
      value_setst::valuest values_op0;
      value_setst::valuest values_op1;
      
      value_set.get_value_set(op0, values_op0, ns);
      value_set.get_value_set(op1, values_op1, ns);

      if(is_null(op1))
      {
        // search NULL in value_set of lhs
        if(contains_null(values_op0))
        {
          inconclusive=inconclusive || values_op0.size() > 1;
	        result= negated ? (exprt) false_exprt() : (exprt) true_exprt();
        }
        else
        {
          result= negated ? (exprt) true_exprt() : (exprt) false_exprt();
        }
      } 
      else
      {
        // we don't know what to do here
        inconclusive=true;
        result=negated ? (exprt) false_exprt() : (exprt) true_exprt();
      }
    }

    #ifdef DEBUG
    value_setst::valuest values_op0;
    value_setst::valuest values_op1;
    
    if(op0.id()==ID_pointer_object
      && op1.id()==ID_pointer_object)
    {
      value_set.get_value_set(op0.op0(), values_op0, ns);
      value_set.get_value_set(op1.op0(), values_op1, ns);    
    }
    else
    {    
      value_set.get_value_set(op0, values_op0, ns);
      value_set.get_value_set(op1, values_op1, ns);
    }

    std::cout << "op0" << std::endl;
    
    for(exprt e : values_op0)
    {
      std::cout << "  " << from_expr(ns, "  ", e) << std::endl;
    }

    std::cout << "op1" << std::endl;

    for(exprt e : values_op1)
    {
      std::cout << "  " << from_expr(ns, "  ", e) << std::endl;
    }
    #endif

    return result;
  }
  else if(src.id()==ID_invalid_pointer)
  {
    const exprt &op0=src.op0();
    
    value_setst::valuest values_op0;
    
    value_set.get_value_set(op0, values_op0, ns);
   
    if(contains_invalid(values_op0))
    {
      inconclusive=inconclusive || values_op0.size() > 1;    
      result= negated ? (exprt) false_exprt() : (exprt) true_exprt();
    }  
    else
    {
      result= negated ? (exprt) true_exprt() : (exprt) false_exprt();
    }
  
    return result;
  }
  else if(src.id()==ID_not)
  {
    return eval_rec(src.op0(), value_set, !negated, inconclusive);
  }

  if(!src.has_operands())
    return src;

  exprt src2=src;

  // recursive calls on structure of 'src'
  Forall_operands(it, src2)
  {
    exprt tmp_op=eval_rec(*it, value_set, negated, inconclusive);
    *it=tmp_op;
  }

  return src2;
}



/*******************************************************************\

Function: value_set_checkt::eval

  Inputs:

 Outputs:

 Purpose: evaluate a pointer expression

\*******************************************************************/

exprt value_set_checkt::eval(
  const exprt &src,
  const value_sett &value_set,
  bool &inconclusive)
{
  exprt result=eval_rec(src, value_set, false, inconclusive);
  simplify_expr(result, ns);
  return result;
}

/*******************************************************************\

Function: value_set_checkt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_checkt::operator()(
  const goto_programt &goto_program)
{
  forall_goto_program_instructions(i_it, goto_program)
  {
    const source_locationt &location=i_it->source_location;
    
    if(location.is_nil() || location.get_file()==irep_idt())
      continue;

    const goto_programt::instructiont &instruction=*i_it;

    if(instruction.is_assert())
    {

      // find value set
      const value_sett
     	  &value_set=value_set_analysis[i_it].value_set;

      irep_idt 
        property_name=instruction.source_location.get_property_id();

      property_entryt 
        &property_entry=property_map[property_name];

      property_entry.description=location.as_string() 
        + from_expr(ns, "", instruction.guard);

      bool inconclusive=false;

      exprt result=eval(instruction.guard, value_set, inconclusive);

      if(result.is_false() && inconclusive)
        property_entry.status=INCONCLUSIVE;
      else
        property_entry.status=result.is_true() ? PASS : FAIL;
    }
  }
}

/*******************************************************************\

Function: value_set_checkt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


void value_set_checkt::output(std::ostream &out) const
{
  unsigned
    nr_pass = 0,
    nr_fail = 0,
    nr_inconclusive = 0;

  // count outcomes
  for(property_mapt::const_iterator
      it=property_map.begin();
      it!=property_map.end();
      ++it)
  {
    property_entryt e=it->second;
  
    switch(e.status)
    {
      case PASS:
        ++nr_pass;
        break;
      case FAIL:
        ++nr_fail;
        break;
      case INCONCLUSIVE:
        ++nr_inconclusive;
        break;
    }
  }

  out << "Value set check: properties " 
    << nr_pass << " passed " 
    << nr_fail << " failed "
    << nr_inconclusive << " inconclusive\n";

}

/*******************************************************************\

Function: value_set_checkt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

  
void value_set_checkt::convert(xmlt &dest) const
{
  dest=xmlt("value_set_check");

  for(property_mapt::const_iterator
      it=property_map.begin();
      it!=property_map.end();
      ++it)
  {
    property_entryt e=it->second;

    xmlt &f=dest.new_element("property");
    f.new_element("id").data=id2string(it->first);
    f.new_element("description").data=id2string(e.description);
    
    switch(e.status)
    {
      case PASS:
        f.new_element("status").data="PASS";
        break;
        
      case FAIL:
        f.new_element("status").data="FAIL";
        break;
        
      case INCONCLUSIVE:
        f.new_element("status").data="INCONCLUSIVE";
        break;
    }
  }
}
  

/*******************************************************************\

Function: show_value_set_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_value_set_check(
  ui_message_handlert::uit ui,
  const value_set_checkt &value_set_check)
{
  switch(ui)
  {
  case ui_message_handlert::XML_UI:
    {
      xmlt xml;
      value_set_check.convert(xml);
      std::cout << xml << std::endl;
    }
    break;
    
  case ui_message_handlert::PLAIN:
    value_set_check.output(std::cout);
    break;
      
  default:;
  }
}


