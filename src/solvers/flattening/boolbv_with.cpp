/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/base_type.h>

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_with

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_with(const exprt &expr, bvt &bv)
{
  if(expr.operands().size()<3)
    throw "with takes at least three operands";

  if((expr.operands().size()%2)!=1)
    throw "with takes an odd number of operands";

  bv=convert_bv(expr.op0());

  unsigned width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr, bv);

  if(bv.size()!=width)
    throw "unexpected operand 0 width";

  bvt prev_bv;
  prev_bv.resize(width);

  const exprt::operandst &ops=expr.operands();

  for(unsigned op_no=1; op_no<ops.size(); op_no+=2)
  {
    bv.swap(prev_bv);

    convert_with(expr.op0().type(),
                 ops[op_no],
                 ops[op_no+1],
                 prev_bv,
                 bv);
  }
}

/*******************************************************************\

Function: boolbvt::convert_with

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_with(
  const typet &type,
  const exprt &op1,
  const exprt &op2,
  const bvt &prev_bv,
  bvt &next_bv)
{
  // we only do that on arrays, bitvectors, structs, and unions

  next_bv.resize(prev_bv.size());

  if(type.id()==ID_array)
    return convert_with_array(to_array_type(type), op1, op2, prev_bv, next_bv);
  else if(type.id()==ID_bv ||
          type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv)
    return convert_with_bv(type, op1, op2, prev_bv, next_bv);
  else if(type.id()==ID_struct)
    return convert_with_struct(to_struct_type(type), op1, op2, prev_bv, next_bv);
  else if(type.id()==ID_union)
    return convert_with_union(to_union_type(type), op1, op2, prev_bv, next_bv);
  else if(type.id()==ID_symbol)
    return convert_with(ns.follow(type), op1, op2, prev_bv, next_bv);

  throw "unexpected with type: "+id2string(type.id());
}

/*******************************************************************\

Function: boolbvt::convert_with_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_with_array(
  const array_typet &type,
  const exprt &op1,
  const exprt &op2,
  const bvt &prev_bv,
  bvt &next_bv)
{
  if(is_unbounded_array(type))
  {
    // can't do this    
    throw "convert_with_array called for unbounded array";
  }

  const exprt &array_size=type.size();

  mp_integer size;

  if(to_integer(array_size, size))
    throw "convert_with_array expects constant array size";
    
  const bvt &op2_bv=convert_bv(op2);

  if(size*op2_bv.size()!=prev_bv.size())
    throw "convert_with_array: unexpected operand 2 width";

  mp_integer op1_value;
  if(!to_integer(op1, op1_value))
  {
    next_bv=prev_bv;

    if(op1_value<size)
    {
      unsigned offset=integer2long(op1_value*op2_bv.size());

      for(unsigned j=0; j<op2_bv.size(); j++)
        next_bv[offset+j]=op2_bv[j];
    }

    return;
  }

  typet counter_type=op1.type();

  for(mp_integer i=0; i<size; i=i+1)
  {
    exprt counter=from_integer(i, counter_type);

    literalt eq_lit=convert(equal_exprt(op1, counter));

    unsigned offset=integer2long(i*op2_bv.size());

    for(unsigned j=0; j<op2_bv.size(); j++)
      next_bv[offset+j]=
        prop.lselect(eq_lit, op2_bv[j], prev_bv[offset+j]);
  }
}

/*******************************************************************\

Function: boolbvt::convert_with_bv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_with_bv(
  const typet &type,
  const exprt &op1,
  const exprt &op2,
  const bvt &prev_bv,
  bvt &next_bv)
{
  literalt l=convert(op2);

  mp_integer op1_value;
  if(!to_integer(op1, op1_value))
  {
    next_bv=prev_bv;

    if(op1_value<next_bv.size())
      next_bv[integer2long(op1_value)]=l;

    return;
  }

  typet counter_type=op1.type();

  for(unsigned i=0; i<prev_bv.size(); i++)
  {
    exprt counter=from_integer(i, counter_type);

    literalt eq_lit=convert(equal_exprt(op1, counter));

    next_bv[i]=prop.lselect(eq_lit, l, prev_bv[i]);
  }
}

/*******************************************************************\

Function: boolbvt::convert_with

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_with_struct(
  const struct_typet &type,
  const exprt &op1,
  const exprt &op2,
  const bvt &prev_bv,
  bvt &next_bv)
{
  next_bv=prev_bv;

  const bvt &op2_bv=convert_bv(op2);

  const irep_idt &component_name=op1.get(ID_component_name);
  const struct_typet::componentst &components=
    type.components();

  unsigned offset=0;

  for(struct_typet::componentst::const_iterator
      it=components.begin();
      it!=components.end();
      it++)
  {

    const typet &subtype=it->type();

    unsigned sub_width=boolbv_width(subtype);

    if(it->get_name()==component_name)
    {
      if(!base_type_eq(subtype, op2.type(), ns))
        throw "with/struct: component `"+id2string(component_name)+
          "' type does not match: "+
          subtype.to_string()+" vs. "+
          op2.type().to_string();

      if(sub_width!=op2_bv.size())
        throw "convert_with_struct: unexpected operand op2 width";

      for(unsigned i=0; i<sub_width; i++)
        next_bv[offset+i]=op2_bv[i];
        
      break; // done
    }

    offset+=sub_width;
  }
}

/*******************************************************************\

Function: boolbvt::convert_with_union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_with_union(
  const union_typet &type,
  const exprt &op1,
  const exprt &op2,
  const bvt &prev_bv,
  bvt &next_bv)
{
  next_bv=prev_bv;

  const bvt &op2_bv=convert_bv(op2);

  if(next_bv.size()<op2_bv.size())
    throw "convert_with_union: unexpected operand op2 width";

  for(unsigned i=0; i<op2_bv.size(); i++)
    next_bv[i]=op2_bv[i];
}

