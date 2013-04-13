/*******************************************************************\

Module: Traces of GOTO Programs in VCD (Value Change Dump) Format

Author: Daniel Kroening

Date: June 2011

\*******************************************************************/

#include <time.h>

#include <cassert>

#include <util/arith_tools.h>
#include <util/pointer_offset_size.h>
#include <util/numbering.h>

#include "vcd_goto_trace.h"

/*******************************************************************\

Function: output_vcd

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string as_vcd_binary(
  const exprt &expr,
  const namespacet &ns)
{
  const typet &type=ns.follow(expr.type());
  
  if(expr.id()==ID_constant)
  {
    if(type.id()==ID_unsignedbv ||
       type.id()==ID_signedbv ||
       type.id()==ID_bv ||
       type.id()==ID_fixedbv ||
       type.id()==ID_floatbv ||
       type.id()==ID_pointer)
      return expr.get_string(ID_value);
  }
  else if(expr.id()==ID_array)
  {
    std::string result;

    forall_operands(it, expr)
      result+=as_vcd_binary(*it, ns);
    
    return result;
  }
  else if(expr.id()==ID_struct)
  {
    std::string result;

    forall_operands(it, expr)
      result+=as_vcd_binary(*it, ns);
    
    return result;
  }
  else if(expr.id()==ID_union)
  { 
    assert(expr.operands().size()==1);
    return as_vcd_binary(expr.op0(), ns);
  }
  
  // build "xxx"

  mp_integer width;

  if(type.id()==ID_unsignedbv ||
     type.id()==ID_signedbv ||
     type.id()==ID_floatbv ||
     type.id()==ID_fixedbv ||
     type.id()==ID_pointer ||
     type.id()==ID_bv)
    width=string2integer(type.get_string(ID_width));
  else
    width=pointer_offset_size(ns, type)*8;

  if(width>=0)
  {
    std::string result;

    for(; width!=0; --width)
      result+='x';

    return result;
  }
  
  return "";
}

/*******************************************************************\

Function: output_vcd

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void output_vcd(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  std::ostream &out)
{
  time_t t;
  time(&t);
  out << "$date\n  " << ctime(&t) << "$end" << std::endl;
  
  // this is pretty arbitrary
  out << "$timescale 1 ns $end" << std::endl;

  // we first collect all variables that are assigned
  
  numbering<irep_idt> n;

  for(goto_tracet::stepst::const_iterator
      it=goto_trace.steps.begin();
      it!=goto_trace.steps.end();
      it++)
  {
    if(it->is_assignment())
    {
      irep_idt identifier=it->lhs_object.get_identifier();
      const typet &type=it->lhs_object.type();
        
      unsigned number=n.number(identifier);

      mp_integer width;

      if(type.id()==ID_bool)
        width=1;
      else if(type.id()==ID_unsignedbv ||
              type.id()==ID_signedbv ||
              type.id()==ID_floatbv ||
              type.id()==ID_fixedbv ||
              type.id()==ID_pointer ||
              type.id()==ID_bv)
        width=string2integer(type.get_string(ID_width));
      else
        width=pointer_offset_size(ns, type)*8;
        
      if(width>=1)
        out << "$var reg " << width << " V" << number << " "
            << identifier << " $end" << std::endl;
    }
  }  

  // end of header
  out << "$enddefinitions $end" << std::endl;

  unsigned timestamp=0;

  for(goto_tracet::stepst::const_iterator
      it=goto_trace.steps.begin();
      it!=goto_trace.steps.end();
      it++)
  {
    switch(it->type)
    {
    case goto_trace_stept::ASSIGNMENT:
      {
        irep_idt identifier=it->lhs_object.get_identifier();
        const typet &type=it->lhs_object.type();

        out << '#' << timestamp << std::endl;
        timestamp++;

        unsigned number=n.number(identifier);
        
        // booleans are special in VCD
        if(type.id()==ID_bool)
        {
          if(it->lhs_object_value.is_true())
            out << "1" << "V" << number << std::endl;
          else if(it->lhs_object_value.is_false())
            out << "0" << "V" << number << std::endl;
          else
            out << "x" << "V" << number << std::endl;
        }
        else
        {
          std::string binary=as_vcd_binary(it->lhs_object_value, ns);

          if(binary!="")
            out << "b" << binary << " V" << number << " " << std::endl;
        }
      }
      break;
      
    default:;
    }
  }
}
