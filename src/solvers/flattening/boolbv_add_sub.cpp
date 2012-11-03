/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <std_types.h>

#include "boolbv.h"

#include "../floatbv/float_utils.h"

/*******************************************************************\

Function: boolbvt::convert_add_sub

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_add_sub(const exprt &expr, bvt &bv)
{
  const typet &type=ns.follow(expr.type());
  
  if(type.id()!=ID_unsignedbv &&
     type.id()!=ID_signedbv &&
     type.id()!=ID_fixedbv &&
     type.id()!=ID_floatbv &&
     type.id()!=ID_range &&
     type.id()!=ID_complex &&
     type.id()!=ID_vector)
    return conversion_failed(expr, bv);

  unsigned width=boolbv_width(type);
  
  if(width==0)
    return conversion_failed(expr, bv);
    
  const exprt::operandst &operands=expr.operands();

  if(operands.size()==0)
    throw "operand "+expr.id_string()+" takes at least one operand";

  const exprt &op0=expr.op0();

  if(op0.type()!=type)
  {
    std::cerr << expr.pretty() << std::endl;
    throw "add/sub with mixed types";
  }

  bv=convert_bv(op0);

  if(bv.size()!=width)
    throw "convert_add_sub: unexpected operand 0 width";

  bool subtract=(expr.id()==ID_minus ||
                 expr.id()=="no-overflow-minus");
                 
  bool no_overflow=(expr.id()=="no-overflow-plus" ||
                    expr.id()=="no-overflow-minus");

  typet arithmetic_type=
    (type.id()==ID_vector || type.id()==ID_complex)?
      ns.follow(type.subtype()):type;

  bv_utilst::representationt rep=
    (arithmetic_type.id()==ID_signedbv ||
     arithmetic_type.id()==ID_fixedbv)?bv_utilst::SIGNED:
                                       bv_utilst::UNSIGNED;

  for(exprt::operandst::const_iterator
      it=operands.begin()+1;
      it!=operands.end(); it++)
  {
    if(it->type()!=type)
    {
      std::cerr << expr.pretty() << std::endl;
      throw "add/sub with mixed types";
    }

    const bvt &op=convert_bv(*it);

    if(op.size()!=width)
      throw "convert_add_sub: unexpected operand width";

    if(type.id()==ID_vector || type.id()==ID_complex)
    {
      const typet &subtype=ns.follow(type.subtype());
    
      unsigned sub_width=boolbv_width(subtype);

      if(sub_width==0 || width%sub_width!=0)
        throw "convert_add_sub: unexpected vector operand width";

      unsigned size=width/sub_width;
      bv.resize(width);

      for(unsigned i=0; i<size; i++)
      {
        bvt tmp_op;
        tmp_op.resize(sub_width);

        for(unsigned j=0; j<tmp_op.size(); j++)
        {
          assert(i*sub_width+j<op.size());
          tmp_op[j]=op[i*sub_width+j];
        }
        
        bvt tmp_result;
        tmp_result.resize(sub_width);

        for(unsigned j=0; j<tmp_result.size(); j++)
        {
          assert(i*sub_width+j<bv.size());
          tmp_result[j]=bv[i*sub_width+j];
        }
        
        if(type.subtype().id()==ID_floatbv)
        {
          float_utilst float_utils(prop);
          float_utils.spec=to_floatbv_type(subtype);
          tmp_result=float_utils.add_sub(tmp_result, tmp_op, subtract);
        }
        else
          tmp_result=bv_utils.add_sub(tmp_result, tmp_op, subtract);
      
        assert(tmp_result.size()==sub_width);
        
        for(unsigned j=0; j<tmp_result.size(); j++)
        {
          assert(i*sub_width+j<bv.size());
          bv[i*sub_width+j]=tmp_result[j];
        }
      }
    }
    else if(type.id()==ID_floatbv)
    {
      float_utilst float_utils(prop);
      float_utils.spec=to_floatbv_type(arithmetic_type);
      bv=float_utils.add_sub(bv, op, subtract);
    }
    else if(no_overflow)
      bv=bv_utils.add_sub_no_overflow(bv, op, subtract, rep);
    else
      bv=bv_utils.add_sub(bv, op, subtract);
  }
}

