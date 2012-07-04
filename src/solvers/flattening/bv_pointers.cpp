/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <i2string.h>
#include <config.h>
#include <c_misc.h>
#include <arith_tools.h>
#include <prefix.h>
#include <std_expr.h>
#include <expr_util.h>
#include <pointer_offset_size.h>
#include <threeval.h>

#include "bv_pointers.h"

/*******************************************************************\

Function: bv_pointerst::convert_rest

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt bv_pointerst::convert_rest(const exprt &expr)
{
  if(expr.type().id()!=ID_bool)
    throw "bv_pointerst::convert_rest got non-boolean operand";

  const exprt::operandst &operands=expr.operands();

  if(expr.id()=="invalid-pointer")
  {
    if(operands.size()==1 &&
       is_ptr(operands[0].type()))
    {
      const bvt &bv=convert_bv(operands[0]);
      
      if(bv.size()!=0)
      {
        bvt invalid_bv, null_bv;
        encode(pointer_logic.get_invalid_object(), invalid_bv);
        encode(pointer_logic.get_null_object(),    null_bv);

        bvt equal_invalid_bv, equal_null_bv;
        equal_invalid_bv.resize(object_bits);
        equal_null_bv.resize(object_bits);

        for(unsigned i=0; i<object_bits; i++)
        {
          equal_invalid_bv[i]=prop.lequal(bv[offset_bits+i],
                                          invalid_bv[offset_bits+i]);
          equal_null_bv[i]   =prop.lequal(bv[offset_bits+i],
                                          null_bv[offset_bits+i]);
        }

        literalt equal_invalid=prop.land(equal_invalid_bv);
        literalt equal_null=prop.land(equal_null_bv);

        return prop.lor(equal_invalid, equal_null);
      }
    }
  }
  else if(expr.id()==ID_dynamic_object)
  {
    if(operands.size()==1 &&
       is_ptr(operands[0].type()))
    {
      bvt bv=convert_bv(operands[0]);
      
      {
        bv.erase(bv.begin(), bv.begin()+offset_bits);

        // for now, allocate literal and then do later
        is_dynamic_objectt is_dynamic_object;
        is_dynamic_object.bv=bv;
        is_dynamic_object.l=prop.new_variable();
        
        is_dynamic_object_list.push_back(is_dynamic_object);
        return is_dynamic_object.l;
      }
    }
  }
  else if(expr.id()==ID_same_object)
  {
    if(operands.size()==2 &&
       is_ptr(operands[0].type()) &&
       is_ptr(operands[1].type()))
    {
      const bvt &bv0=convert_bv(operands[0]);
      const bvt &bv1=convert_bv(operands[1]);

      {
        bvt equal_bv;
        equal_bv.resize(object_bits);

        for(unsigned i=0; i<object_bits; i++)
          equal_bv[i]=prop.lequal(bv0[offset_bits+i],
                                  bv1[offset_bits+i]);

        return prop.land(equal_bv);
      }
    }
  }
  else if(expr.id()==ID_lt || expr.id()==ID_le ||
          expr.id()==ID_gt || expr.id()==ID_ge)
  {
    if(operands.size()==2 &&
       is_ptr(operands[0].type()) &&
       is_ptr(operands[1].type()))
    {
      const bvt &bv0=convert_bv(operands[0]);
      const bvt &bv1=convert_bv(operands[1]);

      const irep_idt rel=expr.id();

      if(rel==ID_le || rel==ID_lt)
        return bv_utils.lt_or_le(rel==ID_le, bv0, bv1, bv_utilst::UNSIGNED);

      if(rel==ID_ge || rel==ID_gt)
        return bv_utils.lt_or_le(rel==ID_ge, bv1, bv0, bv_utilst::UNSIGNED);
                                            // swapped
      assert(false);
    }
  }

  return SUB::convert_rest(expr);
}

/*******************************************************************\

Function: bv_pointerst::bv_pointerst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bv_pointerst::bv_pointerst(
  const namespacet &_ns,
  propt &_prop):
  boolbvt(_ns, _prop),
  pointer_logic(_ns)
{
  object_bits=BV_ADDR_BITS;
  offset_bits=config.ansi_c.pointer_width-object_bits;
  bits=config.ansi_c.pointer_width;
}

/*******************************************************************\

Function: bv_pointerst::convert_address_of_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bv_pointerst::convert_address_of_rec(
  const exprt &expr,
  bvt &bv)
{
  if(expr.id()==ID_symbol)
  {
    add_addr(expr, bv);
    return false;
  }
  else if(expr.id()==ID_label)
  {
    add_addr(expr, bv);
    return false;
  }
  else if(expr.id()=="NULL-object")
  {
    encode(pointer_logic.get_null_object(), bv);
    return false;
  }
  else if(expr.id()==ID_index)
  {
    if(expr.operands().size()!=2)
      throw "index takes two operands";

    const index_exprt &index_expr=to_index_expr(expr);
    const exprt &array=index_expr.array();
    const exprt &index=index_expr.index();
    const typet &array_type=ns.follow(array.type());
    
    // recursive call
    if(array_type.id()==ID_pointer)
    {
      // this should be gone
      convert_pointer_type(array, bv);
      assert(bv.size()==bits);
    }
    else if(array_type.id()==ID_array ||
            array_type.id()==ID_incomplete_array ||
            array_type.id()==ID_string_constant)
    {
      if(convert_address_of_rec(array, bv)) return true;
      assert(bv.size()==bits);
    }
    else
      assert(false);
      
    // get size
    mp_integer size=
      pointer_offset_size(ns, array_type.subtype());
    
    offset_arithmetic(bv, size, index);
    assert(bv.size()==bits);
    return false;
  }
  else if(expr.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(expr);
    const exprt &struct_op=member_expr.op0();
    const typet &struct_op_type=ns.follow(struct_op.type());

    // recursive call
    if(convert_address_of_rec(struct_op, bv))
      return true;

    if(struct_op_type.id()==ID_struct)
    {
      mp_integer offset=member_offset(ns,
        to_struct_type(struct_op_type),
        member_expr.get_component_name());

      // add offset
      offset_arithmetic(bv, offset);
    }
    else if(struct_op_type.id()==ID_union)
    {
      // nothing to do, all members have offset 0
    }
    else
      throw "member takes struct or union operand";

    return false;
  }
  else if(expr.id()==ID_constant ||
          expr.id()==ID_string_constant ||
          expr.id()=="zero_string")
  { // constant
    add_addr(expr, bv);
    return false;
  }
  else if(expr.id()==ID_if)
  {
    const if_exprt &ifex=to_if_expr(expr);

    literalt cond=convert(ifex.cond());

    bvt bv1, bv2;

    if(convert_address_of_rec(ifex.true_case(), bv1))
      return true;
      
    if(convert_address_of_rec(ifex.false_case(), bv2))
      return true;

    bv=bv_utils.select(cond, bv1, bv2);

    return false;
  }

  return true;
}

/*******************************************************************\

Function: bv_pointerst::convert_pointer_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_pointerst::convert_pointer_type(const exprt &expr, bvt &bv)
{
  if(!is_ptr(expr.type()))
    throw "convert_pointer_type got non-pointer type";

  bv.resize(bits);

  if(expr.id()==ID_symbol)
  {
    const irep_idt &identifier=to_symbol_expr(expr).get_identifier();
    const typet &type=expr.type();

    for(unsigned i=0; i<bits; i++)
      bv[i]=map.get_literal(identifier, i, type);

    return;
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    Forall_literals(it, bv)
      *it=prop.new_variable();

    return;
  }
  else if(expr.id()==ID_typecast)
  {
    if(expr.operands().size()!=1)
      throw "typecast takes one operand";

    const exprt &op=expr.op0();
    const typet &op_type=ns.follow(op.type());

    if(op_type.id()==ID_pointer)
      return convert_pointer_type(op, bv);
    else if(op_type.id()==ID_signedbv ||
            op_type.id()==ID_unsignedbv ||
            op_type.id()==ID_bool ||
            op_type.id()==ID_c_enum)
    {
      // Cast from integer to pointer.
      // We need to be able to convert the integer 0 to NULL.
      // We just do a zero extension.
      
      const bvt &op_bv=convert_bv(op);
      
      bv=bv_utils.zero_extension(op_bv, bits);

      return;
    }
  }
  else if(expr.id()==ID_if)
  {
    return SUB::convert_if(expr, bv);
  }
  else if(expr.id()==ID_index)
  {
    return SUB::convert_index(to_index_expr(expr), bv);
  }
  else if(expr.id()==ID_member)
  {
    return SUB::convert_member(to_member_expr(expr), bv);
  }
  else if(expr.id()==ID_address_of)
  {
    if(expr.operands().size()!=1)
      throw expr.id_string()+" takes one operand";
      
    if(convert_address_of_rec(expr.op0(), bv))
      return conversion_failed(expr, bv);
      
    assert(bv.size()==bits);
    return;
  }
  else if(expr.id()==ID_constant)
  {
    irep_idt value=to_constant_expr(expr).get_value();

    if(value==ID_NULL)
      encode(pointer_logic.get_null_object(), bv);
    else
    {
      mp_integer i=string2integer(id2string(value), 2);
      bv=bv_utils.build_constant(i, bits);
    }

    return;
  }
  else if(expr.id()==ID_plus)
  {
    // this has to be pointer plus integer
    
    if(expr.operands().size()<2)
      throw "operator + takes at least two operands";

    mp_integer size=0;
    unsigned count=0;

    forall_operands(it, expr)
    {
      if(it->type().id()==ID_pointer)
      {
        count++;
        bv=convert_bv(*it);
        assert(bv.size()==bits);
        size=pointer_offset_size(ns, it->type().subtype());
      }
    }

    if(count==0)
      throw "found no pointer in pointer-type sum";
    else if(count!=1)
      throw "found more than one pointer in sum";

    bvt sum=bv_utils.build_constant(0, bits);

    forall_operands(it, expr)
    {
      if(it->type().id()==ID_pointer) continue;

      if(it->type().id()!=ID_unsignedbv &&
         it->type().id()!=ID_signedbv)
        return conversion_failed(expr, bv);

      bv_utilst::representationt rep=
        it->type().id()==ID_signedbv?bv_utilst::SIGNED:
                                     bv_utilst::UNSIGNED;

      bvt op=convert_bv(*it);

      if(op.size()==0)
        throw "unexpected pointer arithmetic operand width";
      
      // we cut any extra bits off

      if(op.size()>bits)
        op.resize(bits);
      else if(op.size()<bits)
        op=bv_utils.extension(op, bits, rep);
      
      sum=bv_utils.add(sum, op);
    }

    offset_arithmetic(bv, size, sum);

    return;
  }
  else if(expr.id()==ID_minus)
  {
    // this is pointer-integer

    if(expr.operands().size()!=2)
      throw "operator "+expr.id_string()+" takes two operands";

    if(expr.op0().type().id()!=ID_pointer)
      throw "found no pointer in pointer type in difference";

    if(expr.op1().type().id()!=ID_unsignedbv &&
       expr.op1().type().id()!=ID_signedbv)
      return conversion_failed(expr, bv);

    exprt neg_op1=unary_exprt(
      ID_unary_minus, expr.op1(), expr.op1().type());

    bv=convert_bv(expr.op0());
    
    mp_integer element_size=
      pointer_offset_size(ns, expr.op0().type().subtype());
    
    offset_arithmetic(bv, element_size, neg_op1);

    return;
  }
  else if(expr.id()==ID_lshr || 
          expr.id()==ID_shl)
    return SUB::convert_shift(expr, bv);
  else if(expr.id()==ID_bitand ||
          expr.id()==ID_bitor ||
          expr.id()==ID_bitnot)
    return SUB::convert_bitwise(expr, bv);
  else if(expr.id()==ID_concatenation)
    return SUB::convert_concatenation(expr, bv);
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
    return SUB::convert_byte_extract(expr, bv);

  return conversion_failed(expr, bv);
}

/*******************************************************************\

Function: bv_pointerst::convert_bitvector

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_pointerst::convert_bitvector(const exprt &expr, bvt &bv)
{
  if(is_ptr(expr.type()))
    return convert_pointer_type(expr, bv);

  if(expr.id()==ID_minus &&
     expr.operands().size()==2 &&
     expr.op0().type().id()==ID_pointer &&
     expr.op1().type().id()==ID_pointer)
  {
    // pointer minus pointer
    bvt op0=convert_bv(expr.op0());
    bvt op1=convert_bv(expr.op1());

    unsigned width=boolbv_width(expr.type());
    
    if(width==0)
      return conversion_failed(expr, bv);

    // we do a zero extension
    op0=bv_utils.zero_extension(op0, width);
    op1=bv_utils.zero_extension(op1, width);

    bv=bv_utils.sub(op0, op1);
    
    mp_integer element_size=
      pointer_offset_size(ns, expr.op0().type().subtype());
      
    if(element_size!=1)
    {
      bvt element_size_bv=
        bv_utils.build_constant(element_size, bv.size());
      bv=bv_utils.divider(bv, element_size_bv, bv_utilst::SIGNED);
    }

    return;
  }
  else if(expr.id()==ID_pointer_offset &&
          expr.operands().size()==1 &&
          is_ptr(expr.op0().type()))
  {
    bvt op0=convert_bv(expr.op0());

    unsigned width=boolbv_width(expr.type());

    if(width==0)
      return conversion_failed(expr, bv);
      
    // we need to strip off the object part
    op0.resize(offset_bits);

    // we do a sign extension to permit negative offsets
    bv=bv_utils.sign_extension(op0, width);

    return;
  }
  else if(expr.id()==ID_pointer_object &&
          expr.operands().size()==1 &&
          is_ptr(expr.op0().type()))
  {
    bvt op0=convert_bv(expr.op0());

    unsigned width=boolbv_width(expr.type());
    
    if(width==0)
      return conversion_failed(expr, bv);
      
    // erase offset bits
    
    op0.erase(op0.begin()+0, op0.begin()+offset_bits);

    bv=bv_utils.zero_extension(op0, width);

    return;
  }
  else if(expr.id()==ID_typecast &&
          expr.operands().size()==1 &&
          expr.op0().type().id()==ID_pointer)
  {
    // pointer to int
    bvt op0;
    convert_pointer_type(expr.op0(), op0);
  
    // squeeze it in!

    unsigned width=boolbv_width(expr.type());

    if(width==0)
      return conversion_failed(expr, bv);

    bv=bv_utils.zero_extension(op0, width);

    return;
  }

  return SUB::convert_bitvector(expr, bv);
}

/*******************************************************************\

Function: bv_pointerst::bv_get_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt bv_pointerst::bv_get_rec(
  const bvt &bv,
  const std::vector<bool> &unknown,
  unsigned offset,
  const typet &type) const
{
  if(!is_ptr(type))
    return SUB::bv_get_rec(bv, unknown, offset, type);

  std::string value_addr, value_offset, value;

  for(unsigned i=0; i<bits; i++)
  {
    char ch;
    unsigned bit_nr=i+offset;

    if(unknown[bit_nr])
      ch='0';
    else
      switch(prop.l_get(bv[bit_nr]).get_value())
      {
       case tvt::TV_FALSE: ch='0'; break;
       case tvt::TV_TRUE:  ch='1'; break;
       case tvt::TV_UNKNOWN: ch='0'; break;
       default: assert(false);
      }
      
    value=ch+value;

    if(i<offset_bits)
      value_offset=ch+value_offset;
    else
      value_addr=ch+value_addr;
  }
  
  // we treat these like bit-vector constants, but with
  // some additional annotation

  constant_exprt result(type);
  result.set_value(value);

  pointer_logict::pointert pointer;
  pointer.object=integer2long(binary2integer(value_addr, false));
  pointer.offset=binary2integer(value_offset, true);
  
  // we add the elaborated expression as operand
  result.copy_to_operands(
    pointer_logic.pointer_expr(pointer, type));

  return result;
}

/*******************************************************************\

Function: bv_pointerst::encode

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_pointerst::encode(unsigned addr, bvt &bv)
{
  bv.resize(bits);

  // set offset to zero
  for(unsigned i=0; i<offset_bits; i++)
    bv[i]=const_literal(false);

  // set variable part
  for(unsigned i=0; i<object_bits; i++)
    bv[offset_bits+i]=const_literal(addr&(1<<i));
}

/*******************************************************************\

Function: bv_pointerst::offset_arithmetic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_pointerst::offset_arithmetic(bvt &bv, const mp_integer &x)
{
  bvt bv1=bv;
  bv1.resize(offset_bits); // strip down

  bvt bv2=bv_utils.build_constant(x, offset_bits);

  bvt tmp=bv_utils.add(bv1, bv2);

  // copy offset bits
  for(unsigned i=0; i<offset_bits; i++)
    bv[i]=tmp[i];
}

/*******************************************************************\

Function: bv_pointerst::offset_arithmetic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_pointerst::offset_arithmetic(
  bvt &bv,
  const mp_integer &factor,
  const exprt &index)
{
  bvt bv_index=convert_bv(index);

  bv_utilst::representationt rep=
    index.type().id()==ID_signedbv?bv_utilst::SIGNED:
                                   bv_utilst::UNSIGNED;

  bv_index=bv_utils.extension(bv_index, offset_bits, rep);

  offset_arithmetic(bv, factor, bv_index);
}

/*******************************************************************\

Function: bv_pointerst::offset_arithmetic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_pointerst::offset_arithmetic(
  bvt &bv,
  const mp_integer &factor,
  const bvt &index)
{
  bvt bv_index;
  
  if(factor==1)
    bv_index=index;
  else
  {
    bvt bv_factor=bv_utils.build_constant(factor, index.size());
    bv_index=bv_utils.unsigned_multiplier(index, bv_factor);
  }

  bv_index=bv_utils.zero_extension(bv_index, bv.size());

  bvt bv_tmp=bv_utils.add(bv, bv_index);
  
  // copy lower parts of result
  for(unsigned i=0; i<offset_bits; i++)
    bv[i]=bv_tmp[i];
}

/*******************************************************************\

Function: bv_pointerst::add_addr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_pointerst::add_addr(const exprt &expr, bvt &bv)
{
  unsigned a=pointer_logic.add_object(expr);

  if(a==(unsigned(1)>>object_bits))
    throw "too many variables";

  encode(a, bv);
}

/*******************************************************************\

Function: bv_pointerst::do_is_dynamic_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_pointerst::do_is_dynamic_object(
  const is_dynamic_objectt &is_dynamic_object)
{
  const pointer_logict::objectst &objects=
    pointer_logic.objects;
    
  unsigned number=0;
    
  for(pointer_logict::objectst::const_iterator
      it=objects.begin();
      it!=objects.end();
      it++, number++)
  {
    const exprt &expr=*it;
    
    bool is_dynamic=pointer_logic.is_dynamic_object(expr);
    
    // only compare object part
    bvt bv;
    encode(number, bv);
    
    bv.erase(bv.begin(), bv.begin()+offset_bits);
    
    literalt l1=bv_utils.equal(bv, is_dynamic_object.bv);
    literalt l2=is_dynamic_object.l;
    
    if(!is_dynamic) l2=prop.lnot(l2);
    
    prop.l_set_to(prop.limplies(l1, l2), true);
  }
}

/*******************************************************************\

Function: bv_pointerst::post_process

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_pointerst::post_process()
{
  for(is_dynamic_object_listt::const_iterator
      it=is_dynamic_object_list.begin();
      it!=is_dynamic_object_list.end();
      it++)
    do_is_dynamic_object(*it);
  
  is_dynamic_object_list.clear();
  
  SUB::post_process();
}
