/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: November 2005

\*******************************************************************/

#include <assert.h>

#include <xml_irep.h>
#include <i2string.h>
#include <arith_tools.h>
#include <ieee_float.h>
#include <fixedbv.h>

#include <ansi-c/printf_formatter.h>
#include <langapi/language_util.h>

#include "xml_goto_trace.h"

/*******************************************************************\

Function: convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

xmlt convert(
  const exprt &expr,
  const namespacet &ns)
{
  const typet &type=ns.follow(expr.type());
  xmlt result;
  
  if(expr.id()==ID_constant)
  {
    if(type.id()==ID_unsignedbv ||
       type.id()==ID_signedbv ||
       type.id()==ID_bv)
    {
      result.name="integer";
      result.set_attribute("binary", expr.get_string(ID_value));

      mp_integer i;
      if(!to_integer(expr, i))
        result.data=integer2string(i);
    }
    else if(type.id()==ID_fixedbv)
    {
      result.name="fixed";
      result.set_attribute("binary", expr.get_string(ID_value));
      result.data=fixedbvt(expr).to_ansi_c_string();
    }
    else if(type.id()==ID_floatbv)
    {
      result.name="float";
      result.set_attribute("binary", expr.get_string(ID_value));
      result.data=ieee_floatt(expr).to_ansi_c_string();
    }
    else if(type.id()==ID_pointer)
    {
      result.name="pointer";
      result.set_attribute("binary", expr.get_string(ID_value));
      if(expr.get(ID_value)==ID_NULL)
        result.data="NULL";
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
      e.new_element(convert(*it, ns));
      index++;
    }
  }
  else if(expr.id()==ID_struct)
  {
    result.name="struct";
  
    forall_operands(it, expr)
    {
      xmlt &e=result.new_element("member");
      e.new_element(convert(*it, ns));
    }
  }
  else if(expr.id()==ID_union)
  { 
    result.name="union";
    
    assert(expr.operands().size()==1);
    
    xmlt &e=result.new_element("member");
    e.new_element(convert(expr.op0(), ns));
  }
  else
    result.name="unknown";

  return result;
}

/*******************************************************************\

Function: convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  xmlt &xml)
{
  xml=xmlt("goto_trace");
  
  xml.new_element("mode").data=goto_trace.mode;

  locationt previous_location;

  for(goto_tracet::stepst::const_iterator
      it=goto_trace.steps.begin();
      it!=goto_trace.steps.end();
      it++)
  {
    const locationt &location=it->pc->location;
    
    xmlt xml_location;
    if(location.is_not_nil() && location.get_file()!="")
    {
      xml_location.new_element("file").data=id2string(location.get_file());
      xml_location.new_element("line").data=id2string(location.get_line());
      xml_location.name="location";
    }
    
    switch(it->type)
    {
    case goto_trace_stept::ASSERT:
      if(!it->cond_value)
      {
        xmlt &xml_failure=xml.new_element("failure");
        xml_failure.new_element("reason").data=id2string(it->comment);
        
        xml_failure.new_element("thread").data=i2string(it->thread_nr);

        if(xml_location.name!="")
          xml_failure.new_element().swap(xml_location);
      }
      break;
      
    case goto_trace_stept::ASSIGNMENT:
      {
        irep_idt identifier;

        if(it->original_lhs.is_not_nil())
          identifier=it->original_lhs.get("identifier");
        else
          identifier=it->lhs.get("identifier");
          
        xmlt &xml_assignment=xml.new_element("assignment");

        if(xml_location.name!="")
          xml_assignment.new_element().swap(xml_location);

        std::string value_string, binary_string, type_string;
        
        if(it->value.is_not_nil())
          value_string=from_expr(ns, identifier, it->value);

        if(it->value.type().is_not_nil())
          type_string=from_type(ns, identifier, it->value.type());

        const symbolt *symbol;
        irep_idt base_name, display_name;

        if(!ns.lookup(identifier, symbol))
        {
          base_name=symbol->base_name;
          display_name=symbol->display_name();
          if(type_string=="")
            type_string=from_type(ns, identifier, symbol->type);

          xml_assignment.new_element("mode").data=id2string(symbol->mode);
        }

        xml_assignment.new_element("thread").data=i2string(it->thread_nr);
        xml_assignment.new_element("identifier").data=id2string(identifier);
        xml_assignment.new_element("base_name").data=id2string(base_name);
        xml_assignment.new_element("display_name").data=id2string(display_name);
        xml_assignment.new_element("value").data=id2string(value_string);
        xml_assignment.new_element("type").data=id2string(type_string);
        xml_assignment.new_element("step_nr").data=i2string(it->step_nr);

        if(it->value.is_not_nil())
          xml_assignment.new_element("value_expression").new_element(convert(it->value, ns));
      }
      break;
      
    case goto_trace_stept::OUTPUT:
      {
        printf_formattert printf_formatter(ns);
        printf_formatter(id2string(it->format_string), it->io_args);
        std::string text=printf_formatter.as_string();
        xmlt &xml_output=xml.new_element("output");
        xml_output.new_element("step_nr").data=i2string(it->step_nr);
        xml_output.new_element("thread").data=i2string(it->thread_nr);
        xml_output.new_element("text").data=text;
        xml_output.new_element().swap(xml_location);

        for(std::list<exprt>::const_iterator
            l_it=it->io_args.begin();
            l_it!=it->io_args.end();
            l_it++)
        {
          xml_output.new_element("value").data=from_expr(ns, "", *l_it);
          xml_output.new_element("value_expression").
            new_element(convert(*l_it, ns));
        }
      }
      break;
      
    case goto_trace_stept::INPUT:
      {
        xmlt &xml_output=xml.new_element("input");
        xml_output.new_element("input_id").data=id2string(it->io_id);
        xml_output.new_element("step_nr").data=i2string(it->step_nr);
        xml_output.new_element("thread").data=i2string(it->thread_nr);
        
        for(std::list<exprt>::const_iterator
            l_it=it->io_args.begin();
            l_it!=it->io_args.end();
            l_it++)
        {
          xml_output.new_element("value").data=from_expr(ns, "", *l_it);
          xml_output.new_element("value_expression").
            new_element(convert(*l_it, ns));
        }
            
        xml_output.new_element().swap(xml_location);
      }
      break;
      
    default:
      if(location!=previous_location)
      {
        // just the location
        if(xml_location.name!="")
        {
          xmlt &xml_location_only=xml.new_element("location-only");
          xml_location_only.new_element("step_nr").data=i2string(it->step_nr);
          xml_location_only.new_element("thread").data=i2string(it->thread_nr);
          xml_location_only.new_element().swap(xml_location);
        }
      }
    }

    if(location.is_not_nil() && location.get_file()!="")
      previous_location=location;
  }
}
