/*******************************************************************\

Module: SMT Backend

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <config.h>
#include <arith_tools.h>
#include <expr_util.h>
#include <std_types.h>
#include <std_expr.h>
#include <i2string.h>
#include <bitvector.h>
#include <fixedbv.h>
#include <pointer_offset_size.h>
#include <base_type.h>

#include <ansi-c/string_constant.h>

#include <langapi/language_util.h>

#include <solvers/flattening/boolbv_width.h>
#include <solvers/flattening/pointer_logic.h>

#include "smt1_conv.h"

/*******************************************************************\

Function: smt1_convt::dec_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt smt1_convt::dec_solve()
{
  smt1_prop.finalize();
  return decision_proceduret::D_ERROR;
}

/*******************************************************************\

Function: smt1_convt::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt smt1_convt::get(const exprt &expr) const
{
  if(expr.id()==ID_symbol)
  {
    const irep_idt &id=to_symbol_expr(expr).get_identifier();

    identifier_mapt::const_iterator it=identifier_map.find(id);

    if(it!=identifier_map.end())
      return it->second.value;
  }

  return static_cast<const exprt &>(get_nil_irep());
}

/*******************************************************************\

Function: smt1_convt::set_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::set_value(
  identifiert &identifier,
  const std::string &v)
{
  identifier.value.make_nil();

  const typet &type=ns.follow(identifier.type);

  if(type.id()==ID_signedbv ||
     type.id()==ID_unsignedbv ||
     type.id()==ID_bv ||
     type.id()==ID_fixedbv)
  {
    assert(v.size()==bv_width(type));
    constant_exprt c(type);
    c.set_value(v);
    identifier.value=c;
  }
  else if(type.id()==ID_bool)
  {
    if(v=="1")
      identifier.value.make_true();
    else if(v=="0")
      identifier.value.make_false();
  }
  else if(type.id()==ID_pointer)
  {
    assert(v.size()==config.ansi_c.pointer_width);
    
    unsigned i=config.ansi_c.pointer_width-BV_ADDR_BITS;

    pointer_logict::pointert p;
    p.object=integer2long(
      binary2integer(
        std::string(v, i, std::string::npos), false));

    p.offset=binary2integer(
      std::string(v, 0, i), true);

    identifier.value=pointer_logic.pointer_expr(p, type);
  }
  else if(type.id()==ID_struct)
  {
    identifier.value=binary2struct(to_struct_type(type), v);
  }
  else if(type.id()==ID_union)
  {
    identifier.value=binary2union(to_union_type(type), v);
  }
}

/*******************************************************************\

Function: smt1_convt::array_index_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet smt1_convt::array_index_type() const
{
  signedbv_typet t;
  t.set_width(array_index_bits);
  return t;
}

/*******************************************************************\

Function: smt1_convt::array_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::array_index(const exprt &expr)
{
  if(expr.type().id()==ID_integer) return convert_expr(expr, true);
  
  typet t=array_index_type();
  if(t==expr.type()) return convert_expr(expr, true);
  exprt tmp(ID_typecast, t);
  tmp.copy_to_operands(expr);
  convert_expr(tmp, true);
}

/*******************************************************************\

Function: smt1_convt::convert_address_of_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_address_of_rec(const exprt &expr)
{
  if(expr.id()==ID_symbol ||
     expr.id()==ID_constant ||
     expr.id()==ID_string_constant ||
     expr.id()==ID_label)
  {
    smt1_prop.out
      << "(concat bv0["
      << config.ansi_c.pointer_width-BV_ADDR_BITS << "] "
      << "bv" << pointer_logic.add_object(expr)
      << "[" << BV_ADDR_BITS << "])";
  }
  else if(expr.id()==ID_index)
  {
    if(expr.operands().size()!=2)
      throw "index takes two operands";

    const exprt &array=to_index_expr(expr).array();
    const exprt &index=to_index_expr(expr).index();

    if(index.is_zero())
    {
      if(array.type().id()==ID_pointer)
        convert_expr(array, true);
      else if(array.type().id()==ID_array)
        convert_address_of_rec(array);
      else
        assert(false);
    }
    else
    {
      // this is really pointer arithmetic
      exprt new_index_expr=expr;
      new_index_expr.op1()=gen_zero(index.type());

      exprt address_of_expr(ID_address_of, pointer_typet());
      address_of_expr.type().subtype()=array.type().subtype();
      address_of_expr.copy_to_operands(new_index_expr);

      exprt plus_expr(ID_plus, address_of_expr.type());
      plus_expr.copy_to_operands(address_of_expr, index);

      convert_expr(plus_expr, true);
    }
  }
  else if(expr.id()==ID_member)
  {
    if(expr.operands().size()!=1)
      throw "member takes one operand";

    const member_exprt &member_expr=to_member_expr(expr);

    const exprt &struct_op=member_expr.struct_op();
    const typet &struct_op_type=ns.follow(struct_op.type());

    if(struct_op_type.id()==ID_struct)
    {
      const struct_typet &struct_type=
        to_struct_type(struct_op_type);

      const irep_idt &component_name=
        member_expr.get_component_name();

      mp_integer offset=member_offset(ns, struct_type, component_name);

      typet index_type(ID_unsignedbv);
      index_type.set(ID_width, config.ansi_c.pointer_width);

      smt1_prop.out << "(bvadd ";
      convert_address_of_rec(struct_op);
      smt1_prop.out << " ";
      convert_expr(from_integer(offset, index_type), true);
      smt1_prop.out << ")";
    }
    else if(struct_op_type.id()==ID_union)
    {
      // these all have offset 0
      convert_address_of_rec(struct_op);
    }
    else
      throw "unexpected type of member operand";
  }
  else if(expr.id()==ID_if)
  {
    assert(expr.operands().size()==3);

    smt1_prop.out << "(ite ";
    convert_expr(expr.op0(), false);
    smt1_prop.out << " ";
    convert_expr(expr.op1(), true);
    smt1_prop.out << " ";
    convert_expr(expr.op2(), true);
    smt1_prop.out << ")";
  }
  else
    throw "don't know how to take address of: "+expr.id_string();
}

/*******************************************************************\

Function: smt1_convt::convert_byte_extract

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_byte_extract(const exprt &expr)
{
  mp_integer i;
  if(to_integer(expr.op1(), i))
    throw "byte_extract takes constant as second parameter";

  unsigned w=boolbv_width(expr.op0().type());

  if(w==0)
    throw "failed to get width of byte_extract operand";

  smt1_prop.out << "";

  mp_integer upper, lower;

  if(expr.id()==ID_byte_extract_little_endian)
  {
    upper = ((i+1)*8)-1;
    lower = i*8;
  }
  else
  {
    mp_integer max=w-1;
    upper = max-(i*8);
    lower = max-((i+1)*8-1);
  }

  smt1_prop.out << "(extract[" << upper << ":" << lower << "] ";
  convert_expr(expr.op0(), true);
  smt1_prop.out << ")";
}

/*******************************************************************\

Function: smt1_convt::convert_byte_update

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_byte_update(const exprt &expr)
{
  assert(expr.operands().size()==3);

  // The situation: expr.op0 needs to be split in 3 parts
  // |<--- L --->|<--- M --->|<--- R --->|
  // where M is the expr.op1'th byte
  // We need to output L expr.op2 R

  mp_integer i;
  if(to_integer(expr.op1(), i))
    throw "byte_update takes constant as second operand";

  unsigned w=boolbv_width(expr.op0().type());

  if(w==0)
    throw "failed to get width of byte_update operand";

  mp_integer upper, lower; // of the byte
  mp_integer max=w-1;

  if(expr.id()==ID_byte_update_little_endian)
  {
    upper = ((i+1)*8)-1;
    lower = i*8;
  }
  else
  {
    upper = max-(i*8);
    lower = max-((i+1)*8-1);
  }

  if(upper==max)
  {
    if(lower==0) // there was only one byte
      convert_expr(expr.op2(), true);
    else // uppermost byte selected, only R needed
    {
      smt1_prop.out << "(concat ";
      convert_expr(expr.op2(), true);
      smt1_prop.out << " (extract[" << lower-1 << ":0] ";
      convert_expr(expr.op0(), true);
      smt1_prop.out << "))";
    }
  }
  else
  {
    if(lower==0) // lowermost byte selected, only L needed
    {
      smt1_prop.out << "(concat ";
      smt1_prop.out << "(extract[" << max << ":" << (upper+1) << "] ";
      convert_expr(expr.op0(), true);
      smt1_prop.out << ") ";
      convert_expr(expr.op2(), true);
      smt1_prop.out << ")";
    }
    else // byte in the middle selected, L & R needed
    {
      smt1_prop.out << "(concat (concat ";
      smt1_prop.out << "(extract[" << max << ":" << (upper+1) << "] ";
      convert_expr(expr.op0(), true);
      smt1_prop.out << ") ";
      convert_expr(expr.op2(), true);
      smt1_prop.out << ") (extract[" << (lower-1) << ":0] ";
      convert_expr(expr.op0(), true);
      smt1_prop.out << "))";
    }
  }

}

/*******************************************************************\

Function: smt1_convt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt smt1_convt::convert(const exprt &expr)
{
  assert(expr.type().id()==ID_bool);

  if(expr.is_true())
    return const_literal(true);
  else if(expr.is_false())
    return const_literal(false);

  smt1_prop.out << std::endl;

  find_symbols(expr);

  literalt l=smt1_prop.new_variable();
  smt1_prop.out << ":assumption ; convert " << std::endl
                << " (iff " << smt1_prop.smt1_literal(l) << " ";
  convert_expr(expr, false);
  smt1_prop.out << ")" << std::endl;

  return l;
}

/*******************************************************************\

Function: smt1_convt::convert_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string smt1_convt::convert_identifier(const irep_idt &identifier)
{
  std::string s=id2string(identifier), dest;
  dest.reserve(s.size());

  for(std::string::const_iterator
      it=s.begin();
      it!=s.end();
      it++)
  {
    char ch=*it;

    if(isalnum(ch) || ch=='.' || ch=='_')
      dest+=ch;
    else if(ch==':')
    {
      std::string::const_iterator next_it(it);
      next_it++;
      if(next_it!=s.end() && *next_it==':')
      {
        dest.append("''");
        it=next_it;
      }
      else
      {
        dest+='\'';
        dest.append(i2string(ch));
        dest+='\'';
      }
    }
    else
    {
      dest+='\'';
      dest.append(i2string(ch));
      dest+='\'';
    }
  }

  return dest;
}

/*******************************************************************\

Function: smt1_convt::convert_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_expr(const exprt &expr, bool bool_as_bv)
{
  if(expr.id()==ID_symbol)
  {
    irep_idt id=to_symbol_expr(expr).get_identifier();
    assert(id!="");

    // boolean symbols may have to be converted
    from_bool_begin(expr.type(), bool_as_bv);

    smt1_prop.out << convert_identifier(id);

    from_bool_end(expr.type(), bool_as_bv);
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    irep_idt id=expr.get(ID_identifier);
    assert(id!="");

    // boolean symbols may have to be converted
    from_bool_begin(expr.type(), bool_as_bv);

    smt1_prop.out << "nondet_" << convert_identifier(id);

    from_bool_end(expr.type(), bool_as_bv);
  }
  else if(expr.id()==ID_typecast)
  {
    convert_typecast(to_typecast_expr(expr), bool_as_bv);
  }
  else if(expr.id()==ID_struct)
  {
    convert_struct(expr);
  }
  else if(expr.id()==ID_union)
  {
    convert_union(expr);
  }
  else if(expr.id()==ID_constant)
  {
    convert_constant(to_constant_expr(expr), bool_as_bv);
  }
  else if(expr.id()==ID_concatenation)
    convert_nary(expr, "concat", true);
  else if(expr.id()==ID_bitand)
    convert_nary(expr, "bvand", true);
  else if(expr.id()==ID_bitor)
    convert_nary(expr, "bvor", true);
  else if(expr.id()==ID_bitxor)
    convert_nary(expr, "bvxor", true);
  else if(expr.id()==ID_bitnand)
    convert_nary(expr, "bvnand", true);
  else if(expr.id()==ID_bitnor)
    convert_nary(expr, "bvnor", true);
  else if(expr.id()==ID_bitnot)
  {
    assert(expr.operands().size()==1);
    smt1_prop.out << "(bvnot ";
    convert_expr(expr.op0(), true);
    smt1_prop.out << ")";
  }
  else if(expr.id()==ID_unary_minus)
  {
    assert(expr.operands().size()==1);

    if(expr.type().id()==ID_rational)
    {
      smt1_prop.out << "(- ";
      convert_expr(expr.op0(), true);
      smt1_prop.out << ")";
    }
    else if(expr.type().id()==ID_integer)
    {
      smt1_prop.out << "(~ ";
      convert_expr(expr.op0(), true);
      smt1_prop.out << ")";
    }
    else
    {
      smt1_prop.out << "(bvneg ";
      convert_expr(expr.op0(), true);
      smt1_prop.out << ")";
    }
  }
  else if(expr.id()==ID_if)
  {
    assert(expr.operands().size()==3);

    // The SMTLIB standard requires a different operator in a boolean context
    if(expr.op1().type().id()==ID_bool && !bool_as_bv)
      smt1_prop.out << "(if_then_else ";
    else
      smt1_prop.out << "(ite ";

    convert_expr(expr.op0(), false);
    smt1_prop.out << " ";
    convert_expr(expr.op1(), bool_as_bv);
    smt1_prop.out << " ";
    convert_expr(expr.op2(), bool_as_bv);
    smt1_prop.out << ")";
  }
  else if(expr.id()==ID_and ||
          expr.id()==ID_or ||
          expr.id()==ID_xor)
  {
    assert(expr.type().id()==ID_bool);
    assert(expr.operands().size()>=2);

    // this may have to be converted
    from_bool_begin(expr.type(), bool_as_bv);

    if(expr.operands().size()>=2)
    {
      smt1_prop.out << "(" << expr.id();
      forall_operands(it, expr)
      {
        smt1_prop.out << " ";
        convert_expr(*it, false);
      }
      smt1_prop.out << ")";
    }
    else
      assert(false);

    // this may have to be converted
    from_bool_end(expr.type(), bool_as_bv);
  }
  else if(expr.id()==ID_implies)
  {
    assert(expr.type().id()==ID_bool);
    assert(expr.operands().size()==2);

    // this may have to be converted
    from_bool_begin(expr.type(), bool_as_bv);

    smt1_prop.out << "(implies ";
    convert_expr(expr.op0(), false);
    smt1_prop.out << " ";
    convert_expr(expr.op1(), false);
    smt1_prop.out << ")";

    // this may have to be converted
    from_bool_end(expr.type(), bool_as_bv);
  }
  else if(expr.id()==ID_not)
  {
    assert(expr.operands().size()==1);

    // this may have to be converted
    from_bool_begin(expr.type(), bool_as_bv);

    smt1_prop.out << "(not ";
    convert_expr(expr.op0(), false);
    smt1_prop.out << ")";

    // this may have to be converted
    from_bool_end(expr.type(), bool_as_bv);
  }
  else if(expr.id()==ID_equal ||
          expr.id()==ID_notequal)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));

    // this may have to be converted
    from_bool_begin(expr.type(), bool_as_bv);

    if(expr.op0().type().id()==ID_bool)
    {
      if(expr.id()==ID_notequal)
        smt1_prop.out << "(xor ";
      else
        smt1_prop.out << "(iff ";

      convert_expr(expr.op0(), false);
      smt1_prop.out << " ";
      convert_expr(expr.op1(), false);
      smt1_prop.out << ")";
    }
    else
    {
      if(expr.id()==ID_notequal)
      {
        smt1_prop.out << "(not (= ";
        convert_expr(expr.op0(), true);
        smt1_prop.out << " ";
        convert_expr(expr.op1(), true);
        smt1_prop.out << "))";
      }
      else
      {
        smt1_prop.out << "(= ";
        convert_expr(expr.op0(), true);
        smt1_prop.out << " ";
        convert_expr(expr.op1(), true);
        smt1_prop.out << ")";
      }
    }

    // this may have to be converted
    from_bool_end(expr.type(), bool_as_bv);
  }
  else if(expr.id()==ID_le ||
          expr.id()==ID_lt ||
          expr.id()==ID_ge ||
          expr.id()==ID_gt)
  {
    convert_relation(expr, bool_as_bv);
  }
  else if(expr.id()==ID_plus)
  {
    convert_plus(expr);
  }
  else if(expr.id()==ID_minus)
  {
    convert_minus(expr);
  }
  else if(expr.id()==ID_div)
  {
    convert_div(expr);
  }
  else if(expr.id()==ID_mod)
  {
    convert_mod(expr);
  }
  else if(expr.id()==ID_mult)
  {
    convert_mul(expr);
  }
  else if(expr.id()==ID_address_of)
  {
    assert(expr.operands().size()==1);
    assert(expr.type().id()==ID_pointer);
    convert_address_of_rec(expr.op0());
  }
  else if(expr.id()=="implicit_address_of" ||
          expr.id()=="reference_to")
  {
    // old stuff
    assert(false);
  }
  else if(expr.id()==ID_array_of)
  {
    assert(expr.type().id()==ID_array);
    assert(expr.operands().size()==1);

    // const array_typet &array_type=to_array_type(expr.type());

    // not really there in SMT, so we replace it
    // this is an over-approximation
    array_of_mapt::const_iterator it=array_of_map.find(expr);
    assert(it!=array_of_map.end());

    smt1_prop.out << it->second;
  }
  else if(expr.id()==ID_index)
  {
    convert_index(to_index_expr(expr), bool_as_bv);
  }
  else if(expr.id()==ID_ashr ||
          expr.id()==ID_lshr ||
          expr.id()==ID_shl)
  {
    assert(expr.operands().size()==2);

    if(expr.type().id()==ID_unsignedbv ||
       expr.type().id()==ID_signedbv ||
       expr.type().id()==ID_bv)
    {
      if(expr.id()==ID_ashr)
        smt1_prop.out << "(bvashr ";
      else if(expr.id()==ID_lshr)
        smt1_prop.out << "(bvlshr ";
      else if(expr.id()==ID_shl)
        smt1_prop.out << "(bvshl ";
      else
        assert(false);

      convert_expr(expr.op0(), true);
      smt1_prop.out << " ";
      
      // SMT1 requires the shift distance to have the same width as
      // the value that is shifted -- odd!

      unsigned width_op0=boolbv_width(expr.op0().type());
      unsigned width_op1=boolbv_width(expr.op1().type());

      if(width_op0==width_op1)
        convert_expr(expr.op1(), true);
      else if(width_op0>width_op1)
      {
        smt1_prop.out << "(zero_extend[" << width_op0-width_op1 << "] ";
        convert_expr(expr.op1(), true);
        smt1_prop.out << ")"; // zero_extend
      }
      else
        throw "unsupported shift-operand widths";
                                                                                                                                                                
      smt1_prop.out << ")";
    }
    else
      throw "unsupported type for "+expr.id_string()+
            ": "+expr.type().id_string();
  }
  else if(expr.id()==ID_with)
  {
    convert_with(expr);
  }
  else if(expr.id()==ID_member)
  {
    convert_member(to_member_expr(expr), bool_as_bv);
  }
  else if(expr.id()==ID_pointer_offset)
  {
    assert(expr.operands().size()==1);
    assert(expr.op0().type().id()==ID_pointer);
    smt1_prop.out << "(zero_extend[" << BV_ADDR_BITS << "] (extract["
                  << (config.ansi_c.pointer_width-1-BV_ADDR_BITS)
                  << ":0] ";
    convert_expr(expr.op0(), true);
    smt1_prop.out << "))";
    assert(bv_width(expr.type())==config.ansi_c.pointer_width);
  }
  else if(expr.id()==ID_pointer_object)
  {
    assert(expr.operands().size()==1);
    assert(expr.op0().type().id()==ID_pointer);
    signed int ext=(int)bv_width(expr.type())-(int)BV_ADDR_BITS;

    if(ext>0)
      smt1_prop.out << "(zero_extend[" << ext << "] ";

    smt1_prop.out << "(extract["
                  << (config.ansi_c.pointer_width-1)
                  << ":"
                  << config.ansi_c.pointer_width-1-BV_ADDR_BITS << "] ";
    convert_expr(expr.op0(), true);
    smt1_prop.out << ")";

    if(ext>0) smt1_prop.out << ")";
  }
  else if(expr.id()=="same-object")
  {
    assert(expr.operands().size()==2);

    // this may have to be converted
    from_bool_begin(expr.type(), bool_as_bv);

    smt1_prop.out << "(= (extract["
                  << (config.ansi_c.pointer_width-1)
                  << ":"
                  << config.ansi_c.pointer_width-BV_ADDR_BITS << "] ";
    convert_expr(expr.op0(), true);
    smt1_prop.out << ")";
    smt1_prop.out << " (extract["
                  << (config.ansi_c.pointer_width-1)
                  << ":"
                  << config.ansi_c.pointer_width-BV_ADDR_BITS << "] ";
    convert_expr(expr.op1(), true);
    smt1_prop.out << "))";

    // this may have to be converted
    from_bool_end(expr.type(), bool_as_bv);
  }
  else if(expr.id()=="is_dynamic_object")
  {
    convert_is_dynamic_object(expr, bool_as_bv);
  }
  else if(expr.id()=="invalid-pointer")
  {
    assert(expr.operands().size()==1);

    // this may have to be converted
    from_bool_begin(expr.type(), bool_as_bv);

    smt1_prop.out << "(= (extract["
                  << (config.ansi_c.pointer_width-1)
                  << ":" << config.ansi_c.pointer_width-BV_ADDR_BITS << "] ";
    convert_expr(expr.op0(), true);
    smt1_prop.out << ") bv" << pointer_logic.get_invalid_object()
                  << "[" << BV_ADDR_BITS << "])";

    // this may have to be converted
    from_bool_end(expr.type(), bool_as_bv);
  }
  else if(expr.id()=="pointer_object_has_type")
  {
    assert(expr.operands().size()==1);

    // this may have to be converted
    from_bool_begin(expr.type(), bool_as_bv);

    smt1_prop.out << "false"; // TODO

    // this may have to be converted
    from_bool_end(expr.type(), bool_as_bv);
  }
  else if(expr.id()==ID_string_constant)
  {
    exprt tmp;
    string2array_mapt::const_iterator fit=string2array_map.find(expr);
    assert(fit!=string2array_map.end());

    convert_expr(fit->second, true);
  }
  else if(expr.id()==ID_extractbit)
  {
    assert(expr.operands().size()==2);

    if(expr.op0().type().id()==ID_unsignedbv ||
       expr.op0().type().id()==ID_signedbv)
    {
      // this may have to be converted
      from_bv_begin(expr.type(), bool_as_bv);

      if(expr.op1().is_constant())
      {
        mp_integer i;
        if(to_integer(expr.op1(), i))
          throw "extractbit: to_integer failed";

        smt1_prop.out << "(extract[" << i << ":" << i << "] ";
        convert_expr(expr.op0(), true);
        smt1_prop.out << ")";
      }
      else
      {
        smt1_prop.out << "(extract[0:0] ";
        // the arguments of the shift need to have the same width
        smt1_prop.out << "(bvlshr ";
        convert_expr(expr.op0(), true);
        typecast_exprt tmp(expr.op0().type());
        tmp.op0()=expr.op1();
        convert_expr(tmp, true);
        smt1_prop.out << "))"; // bvlshr, extract
      }

      // this may have to be converted
      from_bv_end(expr.type(), bool_as_bv);
    }
    else
      throw "unsupported type for "+expr.id_string()+
            ": "+expr.op0().type().id_string();
  }
  else if(expr.id()==ID_replication)
  {
    assert(expr.operands().size()==2);

    mp_integer times;
    if(to_integer(expr.op0(), times))
      throw "replication takes constant as first parameter";

    smt1_prop.out << "(repeat[" << times << "] ";
    convert_expr(expr.op1(), true); // this ensures we have a vector
    smt1_prop.out << ")";
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    convert_byte_extract(expr);
  }
  else if(expr.id()==ID_byte_update_little_endian ||
          expr.id()==ID_byte_update_big_endian)
  {
    convert_byte_update(expr);
  }
  else if(expr.id()==ID_width)
  {
    unsigned result_width=boolbv_width(expr.type());
    
    if(result_width==0)
      throw "conversion failed";

    if(expr.operands().size()!=1)
      throw "width expects 1 operand";

    unsigned op_width=boolbv_width(expr.op0().type());
    
    if(op_width==0)
      throw "conversion failed";

    smt1_prop.out << "bv" << op_width/8 << "[" << result_width << "]";
  }
  else if(expr.id()==ID_abs)
  {
    assert(expr.operands().size()==1);

    unsigned result_width=boolbv_width(expr.type());
    
    if(result_width==0)
      throw "conversion failed";

    const typet &type=expr.type();

    if(type.id()==ID_signedbv ||
       type.id()==ID_fixedbv)
    {
      smt1_prop.out << "(ite (bvslt ";
      convert_expr(expr.op0(), true);
      smt1_prop.out << " bv0[" << result_width << "]) ";
      smt1_prop.out << "(bvneg ";
      convert_expr(expr.op0(), true);
      smt1_prop.out << ") ";
      convert_expr(expr.op0(), true);
      smt1_prop.out << ")";
    }
    else if(type.id()==ID_floatbv)
    {
      smt1_prop.out << "(bvand ";
      convert_expr(expr.op0(), true);
      smt1_prop.out << " bv"
                    << (power(2, result_width-1)-1)
                    << "[" << result_width << "])";
    }
    else
      throw "abs with unsupported operand type";
  }
  else if(expr.id()==ID_isnan)
  {
    assert(expr.operands().size()==1);

    const typet &op_type=expr.op0().type();

    if(op_type.id()==ID_fixedbv)
    {
      from_bool_begin(expr.type(), bool_as_bv);
      smt1_prop.out << "false";
      from_bool_end(expr.type(), bool_as_bv);
    }
    else
      throw "isnan with unsupported operand type";
  }
  else if(expr.id()==ID_isfinite)
  {
    if(expr.operands().size()!=1)
      throw "isfinite expects one operand";

    const typet &op_type=expr.op0().type();

    if(op_type.id()==ID_fixedbv)
    {
      from_bool_begin(expr.type(), bool_as_bv);
      smt1_prop.out << "true";
      from_bool_end(expr.type(), bool_as_bv);
    }
    else
      throw "isfinite with unsupported operand type";
  }
  else if(expr.id()==ID_isinf)
  {
    if(expr.operands().size()!=1)
      throw "isinf expects one operand";

    const typet &op_type=expr.op0().type();

    if(op_type.id()==ID_fixedbv)
    {
      from_bool_begin(expr.type(), bool_as_bv);
      smt1_prop.out << "false";
      from_bool_end(expr.type(), bool_as_bv);
    }
    else
      throw "isinf with unsupported operand type";
  }
  else if(expr.id()==ID_isnormal)
  {
    if(expr.operands().size()!=1)
      throw "isnormal expects one operand";

    const typet &op_type=expr.op0().type();

    if(op_type.id()==ID_fixedbv)
    {
      from_bool_begin(expr.type(), bool_as_bv);
      smt1_prop.out << "true";
      from_bool_end(expr.type(), bool_as_bv);
    }
    else
      throw "isnormal with unsupported operand type";
  }
  else if(expr.id()=="overflow-+" ||
          expr.id()=="overflow--")
  {
    assert(expr.operands().size()==2);
    bool subtract=expr.id()=="overflow--";

    const typet &op_type=expr.op0().type();

    unsigned width=bv_width(op_type);

    if(op_type.id()==ID_signedbv)
    {
      // an overflow occurs if the top two bits of the extended sum differ

      from_bool_begin(expr.type(), bool_as_bv);
      smt1_prop.out << "(let (?sum (";
      smt1_prop.out << (subtract?"bvsub":"bvadd");
      smt1_prop.out << " (sign_extend[1] ";
      convert_expr(expr.op0(), true);
      smt1_prop.out << ")";
      smt1_prop.out << " (sign_extend[1] ";
      convert_expr(expr.op1(), true);
      smt1_prop.out << "))) "; // sign_extend, bvadd/sub let2
      smt1_prop.out << "(not (= "
                      "(extract[" << width << ":" << width << "] ?sum) "
                      "(extract[" << (width-1) << ":" << (width-1) << "] ?sum)";
      smt1_prop.out << ")))"; // =, not, let
      from_bool_end(expr.type(), bool_as_bv);
    }
    else if(op_type.id()==ID_unsignedbv)
    {
      // overflow is simply carry-out
      from_bv_begin(expr.type(), bool_as_bv);
      smt1_prop.out << "(extract[" << width << ":" << width << "] ";
      smt1_prop.out << "(" << (subtract?"bvsub":"bvadd");
      smt1_prop.out << " (zero_extend[1] ";
      convert_expr(expr.op0(), true);
      smt1_prop.out << ")";
      smt1_prop.out << " (zero_extend[1] ";
      convert_expr(expr.op1(), true);
      smt1_prop.out << ")))"; // zero_extend, bvsub/bvadd, extract
      from_bv_end(expr.type(), bool_as_bv);
    }
    else
      throw "overflow check on unknown type: "+op_type.id_string();
  }
  else if(expr.id()=="overflow-*")
  {
    assert(expr.operands().size()==2);
    throw "not yet implemented: overflow-*";
  }
  else if(expr.id()==ID_forall || expr.id()==ID_exists)
  {
    assert(expr.operands().size()==2);
    smt1_prop.out << "(" << expr.id() << " (";
    convert_expr(expr.op0(), bool_as_bv);
    smt1_prop.out << " ";
    if(expr.op0().type().id()==ID_bool)
      smt1_prop.out << "Bool";
    else
      convert_type(expr.op0().type());
    smt1_prop.out << ") ";
    convert_expr(expr.op1(), bool_as_bv);
    smt1_prop.out << ")";
  }
  else if(expr.id()==ID_extractbits)
  {
    assert(expr.operands().size()==3);

    if(expr.op0().type().id()==ID_unsignedbv ||
       expr.op0().type().id()==ID_signedbv ||
       expr.op0().type().id()==ID_bv ||
       expr.op0().type().id()==ID_fixedbv)
    {
      smt1_prop.out << "(extract[";
      convert_expr(expr.op1(), bool_as_bv);
      smt1_prop.out << ":";
      convert_expr(expr.op2(), bool_as_bv);
      smt1_prop.out << "] ";
      convert_expr(expr.op0(), bool_as_bv);
      smt1_prop.out << ")";
    }
    else
      throw "unsupported type for "+expr.id_string()+
            ": "+expr.op0().type().id_string();
  }
  else if(expr.id()==ID_array)
  {
    // array constructor
    array_expr_mapt::const_iterator it=array_expr_map.find(expr);
    assert(it!=array_expr_map.end());

    assert(expr.operands().size()!=0);

    forall_operands(it, expr)
      smt1_prop.out << "(store ";

    smt1_prop.out << it->second;

    unsigned i=0;
    forall_operands(it, expr)
    {
      exprt index=from_integer(i, unsignedbv_typet(array_index_bits));
      smt1_prop.out << " ";
      convert_expr(index, true);
      smt1_prop.out << " ";
      convert_expr(*it, true);
      smt1_prop.out << ")";
      i++;
    }
  }
  else
    throw "smt1_convt::convert_expr: `"+
          expr.id_string()+"' is unsupported";
}

/*******************************************************************\

Function: smt1_convt::convert_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_typecast(const typecast_exprt &expr, bool bool_as_bv)
{
  assert(expr.operands().size()==1);
  const exprt &op=expr.op0();
  const typet &expr_type=ns.follow(expr.type());
  const typet &op_type=ns.follow(op.type());

  if(expr_type.id()==ID_bool)
  {
    // boolean typecasts may have to be converted
    from_bool_begin(expr_type, bool_as_bv);

    // this is comparison with zero
    if(op_type.id()==ID_signedbv ||
       op_type.id()==ID_unsignedbv ||
       op_type.id()==ID_fixedbv ||
       op_type.id()==ID_pointer)
    {
      smt1_prop.out << "(not (= ";
      convert_expr(op, true);
      smt1_prop.out << " ";
      convert_expr(gen_zero(op_type), true);
      smt1_prop.out << "))";
    }
    else
    {
      throw "TODO typecast1 "+op_type.id_string()+" -> bool";
    }

    // boolean typecasts may have to be converted
    from_bool_end(expr_type, bool_as_bv);
  }
  else if(expr_type.id()==ID_signedbv ||
          expr_type.id()==ID_unsignedbv ||
          expr_type.id()==ID_c_enum)
  {
    unsigned to_width=bv_width(expr_type);

    if(op_type.id()==ID_signedbv || // from signedbv
       op_type.id()==ID_unsignedbv || // from unsigedbv
       op_type.id()==ID_c_enum)
    {
      unsigned from_width=bv_width(op_type);

      if(from_width==to_width)
        convert_expr(op, true); // ignore
      else if(from_width<to_width) // extend
      {
        if(op_type.id()==ID_signedbv)
          smt1_prop.out << "(sign_extend[";
        else
          smt1_prop.out << "(zero_extend[";

        smt1_prop.out << (to_width-from_width)
                      << "] ";
        convert_expr(op, true);
        smt1_prop.out << ")";
      }
      else // chop off extra bits
      {
        smt1_prop.out << "(extract[" << (to_width-1) << ":0] ";
        convert_expr(op, true);
        smt1_prop.out << ")";
      }
    }
    else if(op_type.id()==ID_fixedbv) // from fixedbv
    {
      const fixedbv_typet &fixedbv_type=to_fixedbv_type(op_type);

      unsigned from_width=fixedbv_type.get_width();
      unsigned from_integer_bits=fixedbv_type.get_integer_bits();
      unsigned from_fraction_bits=fixedbv_type.get_fraction_bits();

      if(to_width>from_integer_bits)
      {
        smt1_prop.out << "(sign_extend[" << (to_width-from_integer_bits) << "] ";
        smt1_prop.out << "(extract[" << (from_width-1) << ":"
                      << from_fraction_bits << "] ";
        convert_expr(op, true);
        smt1_prop.out << "))";
      }
      else
      {
        smt1_prop.out << "(extract[" << (from_fraction_bits+to_width-1)
                      << ":" << from_fraction_bits << "] ";
        convert_expr(op, true);
        smt1_prop.out << ")";
      }
    }
    else if(op_type.id()==ID_bool) // from boolean
    {
      smt1_prop.out << "(ite ";
      convert_expr(op, false);

      if(expr_type.id()==ID_fixedbv)
      {
        fixedbvt fbt(expr);
        smt1_prop.out << " (concat bv1[" << fbt.spec.integer_bits << "] " <<
                        "bv0[" << fbt.spec.get_fraction_bits() << "]) " <<
                        "bv0[" << fbt.spec.width << "]";
      }
      else
      {
        smt1_prop.out << " bv1[" << to_width << "]";
        smt1_prop.out << " bv0[" << to_width << "]";
      }

      smt1_prop.out << ")";
    }
    else if(op_type.id()==ID_pointer) // from pointer to int
    {
      unsigned from_width=config.ansi_c.pointer_width;

      if(from_width<to_width) // extend
      {
        smt1_prop.out << "(sign_extend[";
        smt1_prop.out << (to_width-from_width)
                      << "] (extract[ " << (to_width-1) << ":0] ";
        convert_expr(op, true);
        smt1_prop.out << "))";
      }
      else // chop off extra bits
      {
        smt1_prop.out << "(extract[" << (to_width-1) << ":0] ";
        convert_expr(op, true);
        smt1_prop.out << ")";
      }
    }
    else
    {
      throw "TODO typecast2 "+op_type.id_string()+
            " -> "+expr_type.id_string();
    }
  }
  else if(expr_type.id()==ID_fixedbv) // to fixedbv
  {
    const fixedbv_typet &fixedbv_type=to_fixedbv_type(expr_type);
    unsigned to_fraction_bits=fixedbv_type.get_fraction_bits();
    unsigned to_integer_bits=fixedbv_type.get_integer_bits();

    if(op_type.id()==ID_unsignedbv ||
       op_type.id()==ID_signedbv ||
       op_type.id()==ID_c_enum)
    {
      unsigned from_width=to_bitvector_type(op_type).get_width();
      smt1_prop.out << "(concat ";

      if(from_width==to_integer_bits)
        convert_expr(op, true);
      else if(from_width>to_integer_bits)
      {
        smt1_prop.out << "(extract[" << (to_integer_bits-1) << ":"
                      << to_fraction_bits << "] ";
        convert_expr(op, true);
        smt1_prop.out << ")";
      }
      else
      {
        assert(from_width<to_integer_bits);
        if(expr_type.id()==ID_unsignedbv)
        {
          smt1_prop.out << "(zero_extend["
                        << (to_integer_bits-from_width) << "] ";
          convert_expr(op, true);
          smt1_prop.out << ")";
        }
        else
        {
          smt1_prop.out << "(sign_extend["
                        << (to_integer_bits-from_width) << "] ";
          convert_expr(op, true);
          smt1_prop.out << ")";
        }
      }

      smt1_prop.out << "bv0[" << to_fraction_bits << "])";
    }
    else if(op_type.id()==ID_bool)
    {
      smt1_prop.out << "(concat (concat bv0[" << (to_integer_bits-1) << "]"
                    << " ";
      convert_expr(op, true); // this returns a 1-bit bit-vector
      smt1_prop.out << ") bv0["
                    << to_fraction_bits
                    << "])";
    }
    else if(op_type.id()==ID_fixedbv)
    {
      const fixedbv_typet &from_fixedbv_type=to_fixedbv_type(op_type);
      unsigned from_fraction_bits=from_fixedbv_type.get_fraction_bits();
      unsigned from_integer_bits=from_fixedbv_type.get_integer_bits();
      unsigned from_width=from_fixedbv_type.get_width();

      // let is only allowed in formulas...
      smt1_prop.out << "(concat ";

      if(to_integer_bits<=from_integer_bits)
      {
        smt1_prop.out << "(extract["
                      << (from_fraction_bits+to_integer_bits-1) << ":"
                      << from_fraction_bits
                      << "] ";
        convert_expr(op, true);
        smt1_prop.out << ")";
      }
      else
      {
        assert(to_integer_bits>from_integer_bits);
        smt1_prop.out << "(sign_extend["
                      << (to_integer_bits-from_integer_bits)
                      << "] (extract["
                      << (from_width-1) << ":"
                      << from_fraction_bits
                      << "] ";
        convert_expr(op, true);
        smt1_prop.out << "))";
      }

      smt1_prop.out << " ";

      if(to_fraction_bits<=from_fraction_bits)
      {
        smt1_prop.out << "(extract["
                      << (from_fraction_bits-1) << ":"
                      << (from_fraction_bits-to_fraction_bits)
                      << "] ";
        convert_expr(op, true);
        smt1_prop.out << ")";
      }
      else
      {
        assert(to_fraction_bits>from_fraction_bits);
        smt1_prop.out << "(concat (extract["
                      << (from_fraction_bits-1) << ":0] ";
        convert_expr(op, true);
        smt1_prop.out << ")"
                      << " bv0[" << to_fraction_bits-from_fraction_bits
                      << "])";
      }

      smt1_prop.out << ")"; // concat
    }
    else
      throw "unexpected typecast to fixedbv";
  }
  else if(expr_type.id()==ID_pointer)
  {
    if(op_type.id()==ID_pointer)
    {
      // this just passes through
      convert_expr(op, true);
    }
    else if(op_type.id()==ID_unsignedbv ||
            op_type.id()==ID_signedbv)
    {
      unsigned from_width=bv_width(op_type);

      if(from_width==config.ansi_c.pointer_width)
        convert_expr(op, true);
      else if(from_width<config.ansi_c.pointer_width)
      {
        smt1_prop.out << "(zero_extend["
                      << (config.ansi_c.pointer_width-from_width)
                      << "] ";
        convert_expr(op, true);
        smt1_prop.out << ")"; // zero_extend
      }
      else // from_width>config.ansi_c.pointer_width
      {
        smt1_prop.out << "(extract["
                      << config.ansi_c.pointer_width
                      << ":0] ";
        convert_expr(op, true);
        smt1_prop.out << ")"; // extract
      }
    }
    else
      throw "TODO typecast3 "+op_type.id_string()+" -> pointer";
  }
  else if(expr_type.id()==ID_range)
  {
    throw "TODO range typecast";
  }
  else
    throw "TODO typecast4 ? -> "+expr_type.id_string();
}

/*******************************************************************\

Function: smt1_convt::convert_struct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_struct(const exprt &expr)
{
  const struct_typet &struct_type=to_struct_type(expr.type());

  const struct_typet::componentst &components=
    struct_type.components();

  assert(components.size()==expr.operands().size());

  assert(!components.empty());

  if(components.size()==1)
    convert_expr(expr.op0(), true);
  else
  {
    unsigned nr_ops=0;

    for(unsigned i=0; i<components.size(); i++)
      if(expr.operands()[i].type().id()!="code")
        nr_ops++;

    for(unsigned i=1; i<nr_ops; i++) // one less
        smt1_prop.out << "(concat ";

    bool first=true;
    for(unsigned i=0; i<components.size(); i++)
    {
      const exprt &op=expr.operands()[i];

      if(op.type().id()!="code")
      {
        if(!first) smt1_prop.out << " ";

        if(op.type().id()==ID_array)
          flatten_array(op);
        else
          convert_expr(op, true);

        if(!first) smt1_prop.out << ")"; // concat
        first=false;
      }
    }
  }
}

/*******************************************************************\

Function: smt1_convt::convert_union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_union(const exprt &expr)
{
  const union_typet &union_type=to_union_type(expr.type());

  assert(expr.operands().size()==1);
  const exprt &op=expr.op0();

  unsigned total_width=boolbv_width(union_type);  
  unsigned member_width=boolbv_width(op.type());

  if(total_width==0)
    throw "failed to get union width for union";

  if(member_width==0)
    throw "failed to get union member width for union";

  if(total_width==member_width)
    convert_expr(op, true);
  else
  {
    // we will pad with zeros, but non-det would be better
    assert(total_width>member_width);
    smt1_prop.out << "(concat ";
    smt1_prop.out << "bv0[" << (total_width-member_width) << "] ";
    convert_expr(op, true);
    smt1_prop.out << ")";
  }
}

/*******************************************************************\

Function: smt1_convt::convert_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_constant(const constant_exprt &expr, bool bool_as_bv)
{
  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv ||
     expr.type().id()==ID_bv ||
     expr.type().id()==ID_c_enum)
  {
    mp_integer value;

    if(to_integer(expr, value))
      throw "failed to convert bitvector constant";

    unsigned width=bv_width(expr.type());

    if(value<0) value=power(2, width)+value;

    smt1_prop.out << "bv" << value
                  << "[" << width << "]";
  }
  else if(expr.type().id()==ID_fixedbv)
  {
    fixedbv_spect spec(to_fixedbv_type(expr.type()));

    std::string v_str=id2string(expr.get(ID_value));
    mp_integer v=binary2integer(v_str, false);

    smt1_prop.out << "bv" << v << "[" << spec.width << "]";
  }
  else if(expr.type().id()==ID_floatbv)
  {
    ieee_float_spect spec(to_floatbv_type(expr.type()));

    std::string v_str=id2string(expr.get(ID_value));
    mp_integer v=binary2integer(v_str, false);

    smt1_prop.out << "bv" << v << "[" << spec.width() << "]";
  }
  else if(expr.type().id()==ID_pointer)
  {
    const irep_idt &value=expr.get(ID_value);

    if(value==ID_NULL)
    {
      smt1_prop.out << "(concat"
                    << " bv0[" << config.ansi_c.pointer_width-BV_ADDR_BITS
                    << "]"
                    << " bv" << pointer_logic.get_null_object()
                    << "[" << BV_ADDR_BITS << "])";
    }
    else
      throw "unknown pointer constant: "+id2string(value);
  }
  else if(expr.type().id()==ID_bool)
  {
    if(expr.is_true())
      smt1_prop.out << (bool_as_bv?"bit1":"true");
    else if(expr.is_false())
      smt1_prop.out << (bool_as_bv?"bit0":"false");
    else
      throw "unknown boolean constant";
  }
  else if(expr.type().id()==ID_array)
  {
    // this should be the 'array' expression
    assert(false);
  }
  else if(expr.type().id()==ID_rational)
  {
    std::string value=expr.get(ID_value).as_string();
    size_t pos=value.find("/");

    if(pos==std::string::npos)
      smt1_prop.out << value << ".0";
    else
    {
      smt1_prop.out << "(/ " << value.substr(0,pos) << ".0 "
                             << value.substr(pos+1) << ".0)";
    }
  }
  else if(expr.type().id()==ID_integer ||
          expr.type().id()==ID_natural)
  {
    std::string value=expr.get(ID_value).as_string();
    
    if(value[0]=='-') 
      smt1_prop.out << "(~ " << value.substr(1) << ")";
    else
      smt1_prop.out << value;
  }
  else
    throw "unknown constant: "+expr.type().id_string();
}

/*******************************************************************\

Function: smt1_convt::convert_mod

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_mod(const exprt &expr)
{
  assert(expr.operands().size()==2);

  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv)
  {
    if(expr.type().id()==ID_unsignedbv)
      smt1_prop.out << "(bvurem ";
    else
      smt1_prop.out << "(bvsrem ";

    convert_expr(expr.op0(), true);
    smt1_prop.out << " ";
    convert_expr(expr.op1(), true);
    smt1_prop.out << ")";
  }
  else
    throw "unsupported type for mod: "+expr.type().id_string();
}

/*******************************************************************\

Function: smt1_convt::convert_is_dynamic_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_is_dynamic_object(
  const exprt &expr,
  bool bool_as_bv)
{
  std::vector<unsigned> dynamic_objects;
  pointer_logic.get_dynamic_objects(dynamic_objects);

  assert(expr.operands().size()==1);

  // this may have to be converted
  from_bool_begin(expr.type(), bool_as_bv);

  if(dynamic_objects.empty())
    smt1_prop.out << "false";
  else
  {
    // let is only allowed in formulas

    smt1_prop.out << "(let (?obj (extract["
                  << (config.ansi_c.pointer_width-1)
                  << ":" << config.ansi_c.pointer_width-BV_ADDR_BITS << "] ";
    convert_expr(expr.op0(), true);
    smt1_prop.out << ")) ";

    if(dynamic_objects.size()==1)
    {
      smt1_prop.out << "(= bv" << dynamic_objects.front()
                    << "[" << BV_ADDR_BITS << "] ?obj)";
    }
    else
    {
      smt1_prop.out << "(or";

      for(std::vector<unsigned>::const_iterator
          it=dynamic_objects.begin();
          it!=dynamic_objects.end();
          it++)
        smt1_prop.out << " (= bv" << *it
                      << "[" << BV_ADDR_BITS << "] ?obj)";

      smt1_prop.out << ")"; // or
    }

    smt1_prop.out << ")"; // let
  }

  // this may have to be converted
  from_bool_end(expr.type(), bool_as_bv);
}

/*******************************************************************\

Function: smt1_convt::convert_relation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_relation(const exprt &expr, bool bool_as_bv)
{
  assert(expr.operands().size()==2);

  // this may have to be converted
  from_bool_begin(expr.type(), bool_as_bv);

  const typet &op_type=expr.op0().type();

  smt1_prop.out << "(";

  if(op_type.id()==ID_unsignedbv)
  {
    if(expr.id()==ID_le)
      smt1_prop.out << "bvule";
    else if(expr.id()==ID_lt)
      smt1_prop.out << "bvult";
    else if(expr.id()==ID_ge)
      smt1_prop.out << "bvuge";
    else if(expr.id()==ID_gt)
      smt1_prop.out << "bvugt";

    smt1_prop.out << " ";
    convert_expr(expr.op0(), true);
    smt1_prop.out << " ";
    convert_expr(expr.op1(), true);
  }
  else if(op_type.id()==ID_signedbv ||
          op_type.id()==ID_fixedbv)
  {
    if(expr.id()==ID_le)
      smt1_prop.out << "bvsle";
    else if(expr.id()==ID_lt)
      smt1_prop.out << "bvslt";
    else if(expr.id()==ID_ge)
      smt1_prop.out << "bvsge";
    else if(expr.id()==ID_gt)
      smt1_prop.out << "bvsgt";

    smt1_prop.out << " ";
    convert_expr(expr.op0(), true);
    smt1_prop.out << " ";
    convert_expr(expr.op1(), true);
  }
  else if(op_type.id()==ID_rational || 
          op_type.id()==ID_integer)
  {
    smt1_prop.out << expr.id();

    smt1_prop.out << " ";
    convert_expr(expr.op0(), true);
    smt1_prop.out << " ";
    convert_expr(expr.op1(), true);
  }
  else
    throw "unsupported type for "+expr.id_string()+
          ": "+op_type.id_string();

  smt1_prop.out << ")";

  // this may have to be converted
  from_bool_end(expr.type(), bool_as_bv);
}

/*******************************************************************\

Function: smt1_convt::convert_plus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_plus(const exprt &expr)
{
  assert(expr.operands().size()>=2);

  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv ||
     expr.type().id()==ID_fixedbv)
  {
    convert_nary(expr, "bvadd", true);
  }
  else if(expr.type().id()==ID_pointer)
  {
    if(expr.operands().size()!=2)
      throw "pointer arithmetic with more than two operands";

    exprt p=expr.op0(), i=expr.op1();

    if(p.type().id()!=ID_pointer)
      p.swap(i);

    if(p.type().id()!=ID_pointer)
      throw "unexpected mixture in pointer arithmetic";

    mp_integer element_size=
      pointer_offset_size(ns, expr.type().subtype());

    smt1_prop.out << "(bvadd ";
    convert_expr(p, true);
    smt1_prop.out << " ";

    if(element_size>=2)
    {
      smt1_prop.out << "(bvmul ";
      convert_expr(i, true);
      smt1_prop.out << " bv" << element_size
                    << "[" << config.ansi_c.pointer_width << "])";
    }
    else
      convert_expr(i, true);

    smt1_prop.out << ")";
  }
  else if(expr.type().id()==ID_rational ||
          expr.type().id()==ID_integer)
  {
    convert_nary(expr, "+", true);
  }  
  else
    throw "unsupported type for +: "+expr.type().id_string();
}

/*******************************************************************\

Function: smt1_convt::convert_minus

  Inputs:

 Outputs:

 Purpose:
e
\*******************************************************************/

void smt1_convt::convert_minus(const exprt &expr)
{
  assert(expr.operands().size()==2);

  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv ||
     expr.type().id()==ID_fixedbv)
  {
    smt1_prop.out << "(bvsub ";

    if(expr.op0().type().id()==ID_pointer)
      smt1_prop.out << "(extract[" << config.ansi_c.pointer_width-1 << ":0] ";
    convert_expr(expr.op0(), true);
    if(expr.op0().type().id()==ID_pointer)
      smt1_prop.out << ")";

    smt1_prop.out << " ";

    if(expr.op1().type().id()==ID_pointer)
      smt1_prop.out << "(extract[" << config.ansi_c.pointer_width-1 << ":0] ";
    convert_expr(expr.op1(), true);
    if(expr.op1().type().id()==ID_pointer)
      smt1_prop.out << ")";

    smt1_prop.out << ")";
  }
  else if(expr.type().id()==ID_pointer)
  {
    convert_expr(binary_exprt(
        expr.op0(),
        "+",
        unary_minus_exprt(expr.op1(), expr.op1().type()),
        expr.type()),
      true);
  }
  else
    throw "unsupported type for -: "+expr.type().id_string();
}

/*******************************************************************\

Function: smt1_convt::convert_div

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_div(const exprt &expr)
{
  assert(expr.operands().size()==2);

  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv)
  {
    if(expr.type().id()==ID_unsignedbv)
      smt1_prop.out << "(bvudiv ";
    else
      smt1_prop.out << "(bvsdiv ";

    convert_expr(expr.op0(), true);
    smt1_prop.out << " ";
    convert_expr(expr.op1(), true);
    smt1_prop.out << ")";
  }
  else if(expr.type().id()==ID_fixedbv)
  {
    fixedbvt fbt(expr);
    unsigned fraction_bits=fbt.spec.get_fraction_bits();

    smt1_prop.out << "(extract[" << fbt.spec.width-1 << ":0] ";
    smt1_prop.out << "(bvsdiv ";

    smt1_prop.out << "(concat ";
    convert_expr(expr.op0(), true);
    smt1_prop.out << " bv0[" << fraction_bits << "]) ";

    smt1_prop.out << "(sign_extend[" << fraction_bits << "] ";
    convert_expr(expr.op1(), true);
    smt1_prop.out << ")";

    smt1_prop.out << "))";
  }
  else
    throw "unsupported type for /: "+expr.type().id_string();
}

/*******************************************************************\

Function: smt1_convt::convert_mul

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_mul(const exprt &expr)
{
  assert(expr.operands().size()>=2);

  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv)
  {
    forall_operands(it, expr)
      if(it!=expr.operands().begin()) smt1_prop.out << "(bvmul ";

    exprt::operandst::const_iterator last;
    forall_operands(it, expr)
    {
      if(it!=expr.operands().begin())
      {
          convert_expr(*last, true);
          smt1_prop.out << " ";
          convert_expr(*it, true);
          smt1_prop.out << ")";
      }
      last = it;
    }
  }
  else if(expr.type().id()==ID_fixedbv)
  {
    fixedbvt fbt(expr);
    unsigned fraction_bits=fbt.spec.get_fraction_bits();

    smt1_prop.out << "(extract[" << fbt.spec.width+fraction_bits-1 << ":"
                                 << fraction_bits << "] ";

    forall_operands(it, expr)
      if(it!=expr.operands().begin()) smt1_prop.out << "(bvmul ";

    exprt::operandst::const_iterator last;
    forall_operands(it, expr)
    {
      smt1_prop.out << "(sign_extend[" << fraction_bits << "] ";
      convert_expr(*it, true);
      smt1_prop.out << ") ";

      if(it!=expr.operands().begin())
        smt1_prop.out << ")";
    }

    smt1_prop.out << ")";
  }
  else if(expr.type().id()==ID_rational)
  {
    smt1_prop.out << "(*";

    forall_operands(it, expr)
    {
      smt1_prop.out << " ";
      convert_expr(*it, true);
    }

    smt1_prop.out << ")";
  }
  else
    throw "unsupported type for *: "+expr.type().id_string();
}

/*******************************************************************\

Function: smt1_convt::convert_with

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_with(const exprt &expr)
{
  assert(expr.operands().size()>=3);
  
  const typet &expr_type=ns.follow(expr.type());

  if(expr_type.id()==ID_array)
  {
    const exprt &array=expr.op0();

    if(array.id()==ID_member)
    {
      // arrays in structs are flattened!
      const typet &array_type=to_array_type(expr.type());
      const typet &elem_type=array_type.subtype();

      const member_exprt &member_expr=to_member_expr(array);
      const exprt &struct_op=member_expr.struct_op();
      const irep_idt &name=member_expr.get_component_name();

      unsigned total_width=boolbv_width(struct_op.type());
      
      if(total_width==0)
        throw "failed to get struct width";

      unsigned offset=boolbv_width.get_member(
        to_struct_type(struct_op.type()), name).offset;

      unsigned width=boolbv_width(expr.type());

      if(width==0)
        throw "failed to get struct member width";

      unsigned elem_width=boolbv_width(elem_type);

      if(elem_width==0)
        throw "failed to get struct width";

      unsigned array_bits=(offset+width) - offset;

      assert(expr.operands().size()==3);
      const exprt &index=expr.operands()[1];
      const exprt &value=expr.operands()[2];

      smt1_prop.out << "(bvor ";
      smt1_prop.out << "(bvand ";

      // this gets us the array
      smt1_prop.out << "(extract[" << offset+width-1 << ":" << offset << "] ";
      convert_expr(struct_op, true);
      smt1_prop.out << ")";

      // the mask
      smt1_prop.out << " (bvnot (bvshl";

      smt1_prop.out << " (concat";
      smt1_prop.out << " (repeat[" << array_bits-elem_width << "] bv0[1])";
      smt1_prop.out << " (repeat[" << elem_width << "] bv1[1])";
      smt1_prop.out << ")"; // concat

      // shift it to the index
      smt1_prop.out << " (zero_extend[" << width-array_index_bits << "]";
      smt1_prop.out << " (bvmul ";
      convert_expr(index, true);
      smt1_prop.out << " bv" << elem_width << "[" << array_index_bits << "]";
      smt1_prop.out << "))))"; // bvmul, bvshl, bvneg

      smt1_prop.out << ")"; // bvand

      // the new value
      smt1_prop.out << " (bvshl (zero_extend[" << array_bits-elem_width << "] ";
      convert_expr(value, true);
      // shift it to the index
      smt1_prop.out << ")";
      smt1_prop.out << " (zero_extend[" << width-array_index_bits << "]";
      smt1_prop.out << " (bvmul ";
      convert_expr(index, true);
      smt1_prop.out << " bv" << elem_width << "[" << array_index_bits << "]";
      smt1_prop.out << ")))"; // bvmul, bvshl, ze

      smt1_prop.out << ")"; // bvor
    }
    else
    {
      smt1_prop.out << "(store ";

      convert_expr(expr.op0(), true);

      for(unsigned i=1; i<expr.operands().size(); i+=2)
      {
        assert((i+1)<expr.operands().size());
        const exprt &index=expr.operands()[i];
        const exprt &value=expr.operands()[i+1];

        smt1_prop.out << " ";
        array_index(index);
        smt1_prop.out << " ";

        // Booleans are put as bv[1] into an array
        convert_expr(value, true);
      }

      smt1_prop.out << ")";
    }
  }
  else if(expr_type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(expr_type);

    if(expr.operands().size()==3)
    {
      const exprt &index=expr.op1();
      const exprt &value=expr.op2();

      unsigned total_width=boolbv_width(expr.type());

      if(total_width==0)
        throw "failed to get struct width for with";

      unsigned width=boolbv_width(value.type());

      if(width==0)
        throw "failed to get member width for with";

      unsigned offset=boolbv_width.get_member(
        struct_type, index.get(ID_component_name)).offset;

      if(total_width==width)
        convert_expr(value, true);
      else
      {
        if(offset+width!=total_width)
        {
          smt1_prop.out << "(concat";
          smt1_prop.out << " (extract[" << (total_width-1) << ":" << (offset+width) << "] ";
          convert_expr(expr.op0(), true);
          smt1_prop.out << ")";
        }

        if(offset!=0) smt1_prop.out << " (concat";

        smt1_prop.out << " ";
        convert_expr(value, true);

        if(offset!=0)
        {
          smt1_prop.out << " (extract[" << (offset-1) << ":0] ";
          convert_expr(expr.op0(), true);
          smt1_prop.out << ")";
          smt1_prop.out << ")"; // concat
        }

        if(offset+width!=total_width) smt1_prop.out << ")"; // concat
      }
    }
    else
    {
      assert(false);
    }
  }
  else if(expr_type.id()==ID_union)
  {
    const union_typet &union_type=to_union_type(expr_type);

    if(expr.operands().size()==3)
    {
      //const exprt &index=expr.op1();
      const exprt &value=expr.op2();

      unsigned total_width=boolbv_width(union_type);
      
      if(total_width==0)
        throw "failed to get union width for with";

      unsigned member_width=boolbv_width(value.type());

      if(member_width==0)
        throw "failed to get union member width for with";

      if(total_width==member_width)
        convert_expr(value, true);
      else
      {
        assert(total_width>member_width);
        smt1_prop.out << "(concat ";
        smt1_prop.out << "(extract["
                      << (total_width-1)
                      << ":" << member_width << "] ";
        convert_expr(expr.op0(), true);
        smt1_prop.out << ") ";
        convert_expr(value, true);
        smt1_prop.out << ")";
      }
    }
    else
    {
      assert(false);
    }
  }
  else
    throw "with expects struct, union, or array type, "
          "but got "+expr.type().id_string();
}

/*******************************************************************\

Function: smt1_convt::convert_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_index(const index_exprt &expr, bool bool_as_bv)
{
  assert(expr.operands().size()==2);

  if(expr.array().id()==ID_member)
  {
    // these were flattened
    const typet &array_type=to_array_type(expr.array().type());
    const typet &elem_type=array_type.subtype();

    const member_exprt &member_expr=to_member_expr(expr.array());
    const exprt &struct_op=member_expr.struct_op();
    //const irep_idt &name=member_expr.get_component_name();

    unsigned total_width=boolbv_width(struct_op.type());
    
    if(total_width==0)
      throw "failed to get struct width";

    //unsigned offset=boolbv_width.get_member(
    //     to_struct_type(struct_op.type()), name).offset;

    unsigned width=boolbv_width(member_expr.type());
    
    if(width==0)
      throw "failed to get struct member width";

    unsigned elem_width=boolbv_width(elem_type);

    if(elem_width==0)
      throw "failed to get struct width";

    smt1_prop.out << "(extract[" << elem_width-1 <<  ":0] ";
    smt1_prop.out << "(bvlshr ";
    convert_expr(expr.array(), true);
    smt1_prop.out << " (zero_extend[" << width-array_index_bits << "]";
    smt1_prop.out << " (bvmul ";
    convert_expr(expr.index(), true);
    smt1_prop.out << " bv" << elem_width << "[" << array_index_bits << "]";
    smt1_prop.out << "))))";
  }
  else
  {
    // Booleans out of arrays may have to be converted
    from_bv_begin(expr.type(), bool_as_bv);

    smt1_prop.out << "(select ";
    convert_expr(expr.array(), true);
    smt1_prop.out << " ";
    array_index(expr.index());
    smt1_prop.out << ")";

    // Booleans out of arrays may have to be converted
    from_bv_end(expr.type(), bool_as_bv);
  }
}

/*******************************************************************\

Function: smt1_convt::convert_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_member(const member_exprt &expr, bool bool_as_bv)
{
  assert(expr.operands().size()==1);

  const member_exprt &member_expr=to_member_expr(expr);
  const exprt &struct_op=member_expr.struct_op();
  const typet &struct_op_type=ns.follow(struct_op.type());
  const irep_idt &name=member_expr.get_component_name();

  // Booleans pulled out of structs may have to be converted
  from_bv_begin(expr.type(), bool_as_bv);

  if(struct_op_type.id()==ID_struct)
  {
    unsigned offset=boolbv_width.get_member(
                      to_struct_type(struct_op_type), name).offset;

    unsigned width=boolbv_width(expr.type());
    
    if(width==0)
      throw "failed to get struct member width";

    smt1_prop.out << "(extract["
                  << (offset+width-1)
                  << ":"
                  << offset
                  << "] ";
    convert_expr(struct_op, true);
    smt1_prop.out << ")";
  }
  else if(struct_op_type.id()==ID_union)
  {
    unsigned width=boolbv_width(expr.type());

    if(width==0)
      throw "failed to get union member width";

    smt1_prop.out << "(extract["
                  << (width-1)
                  << ":0] ";
    convert_expr(struct_op, true);
    smt1_prop.out << ")";
  }
  else
    assert(false);

  // Booleans pulled out of structs may have to be converted
  from_bv_end(expr.type(), bool_as_bv);
}

/*******************************************************************\

Function: smt1_convt::convert_overflow

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_overflow(const exprt &expr)
{
}

/*******************************************************************\

Function: smt1_convt::set_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::set_to(const exprt &expr, bool value)
{
  if(expr.id()==ID_and && value)
  {
    forall_operands(it, expr)
      set_to(*it, true);
    return;
  }

  if(expr.id()==ID_not)
  {
    assert(expr.operands().size()==1);
    return set_to(expr.op0(), !value);
  }

  smt1_prop.out << std::endl;

  find_symbols(expr);

  #if 0
  smt1_prop.out << "; CONV: "
                << from_expr(expr) << std::endl;
  #endif

  smt1_prop.out << ":assumption ; set_to "
                << (value?"true":"false") << std::endl
                << " ";

  assert(expr.type().id()==ID_bool);

  if(!value)
  {
    smt1_prop.out << "(not ";
    convert_expr(expr, false);
    smt1_prop.out << ")";
  }
  else
    convert_expr(expr, false);

  smt1_prop.out << std::endl;
}

/*******************************************************************\

Function: smt1_convt::find_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::find_symbols(const exprt &expr)
{
  find_symbols(expr.type());

  if(expr.id()==ID_forall || expr.id()==ID_exists)
  {
    assert(expr.operands().size()==2);
    assert(expr.op0().id()==ID_symbol);

    const irep_idt &ident=expr.op0().get(ID_identifier);
    quantified_symbols.insert(ident);
    find_symbols(expr.op1());
    quantified_symbols.erase(ident);
  }
  else
    forall_operands(it, expr)
      find_symbols(*it);

  if(expr.id()==ID_symbol ||
     expr.id()==ID_nondet_symbol)
  {
    // we don't track function-typed symbols
    if(expr.type().id()==ID_code)
      return;

    irep_idt identifier;

    if(expr.id()==ID_symbol)
      identifier=to_symbol_expr(expr).get_identifier();
    else
      identifier="nondet_"+id2string(expr.get(ID_identifier));

    if(quantified_symbols.find(identifier)!=quantified_symbols.end())
      return; // Symbol is quantified, i.e., it doesn't require declaration.

    identifiert &id=identifier_map[identifier];

    if(id.type.is_nil())
    {
      id.type=expr.type();

      if(id.type.id()==ID_bool)
      {
        smt1_prop.out << ":extrapreds(("
                      << convert_identifier(identifier)
                      << "))" << std::endl;
      }
      else
      {
        smt1_prop.out << ":extrafuns(("
                      << convert_identifier(identifier)
                      << " ";
        convert_type(expr.type());
        smt1_prop.out << "))" << std::endl;
      }
    }
  }
  else if(expr.id()==ID_array_of)
  {
    if(array_of_map.find(expr)==array_of_map.end())
    {
      irep_idt id="array_of'"+i2string(array_of_map.size());
      smt1_prop.out << "; the following is a poor substitute for lambda i. x" << std::endl;
      smt1_prop.out << ":extrafuns(("
                    << id
                    << " ";
      convert_type(expr.type());
      smt1_prop.out << "))" << std::endl;

      // we can initialize array_ofs if they have
      // a constant size and a constant element
      if(expr.type().find(ID_size)!=get_nil_irep() &&
         expr.op0().id()==ID_constant)
      {
        const array_typet &array_type=to_array_type(expr.type());
        mp_integer size;

        if(!to_integer(array_type.size(), size))
        {
          // since we can't use quantifiers, let's enumerate...
          for(mp_integer i=0; i<size; ++i)
          {
            smt1_prop.out << ":assumption (= (select " << id << " bv" <<
             i << "[" << array_index_bits << "]) ";
            convert_expr(expr.op0(), true);
            smt1_prop.out << ")" << std::endl;
          }
        }
      }

      array_of_map[expr]=id;
    }
  }
  else if(expr.id()==ID_array)
  {
    if(array_expr_map.find(expr)==array_expr_map.end())
    {
      // introduce a temporary array.
      irep_idt id="array_init'"+i2string(array_expr_map.size());
      smt1_prop.out << ":extrafuns(("
                    << id
                    << " ";
      convert_type(expr.type());
      smt1_prop.out << "))" << std::endl;
      array_expr_map[expr]=id;
    }
  }
  else if(expr.id()==ID_string_constant)
  {
    if(string2array_map.find(expr)==string2array_map.end())
    {
      exprt t=to_string_constant(expr).to_array_expr();
      string2array_map[expr]=t;

      // introduce a temporary array.
      irep_idt id="string'"+i2string(array_expr_map.size());
      smt1_prop.out << ":extrafuns(("
                    << id
                    << " ";
      convert_type(t.type());
      smt1_prop.out << "))" << std::endl;
      array_expr_map[t]=id;
    }
  }

}

/*******************************************************************\

Function: smt1_convt::convert_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_type(const typet &type)
{
  if(type.id()==ID_array)
  {    
    const array_typet &array_type=to_array_type(type);
    
    smt1_prop.out << "Array[" << array_index_bits << ":";

    unsigned width=boolbv_width(array_type.subtype());
    
    if(width==0)
      throw "failed to get width of array subtype";

    smt1_prop.out << width << "]";
  }
  else if(type.id()==ID_bool)
  {
    smt1_prop.out << "BitVec[1]";
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union)
  {
    unsigned width=boolbv_width(type);
    
    if(width==0)
      throw "failed to get width of struct/union";

    smt1_prop.out << "BitVec[" << width << "]";
  }
  else if(type.id()==ID_pointer ||
          type.id()==ID_reference)
  {
    unsigned width=boolbv_width(type);

    if(width==0)
      throw "failed to get width of pointer/reference";

    smt1_prop.out << "BitVec[" << width << "]";
  }
  else if(type.id()==ID_bv ||
          type.id()==ID_floatbv ||
          type.id()==ID_fixedbv ||
          type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv ||
          type.id()==ID_c_enum)
  {
    smt1_prop.out << "BitVec[" << type.get(ID_width) << "]";
  }
  else if(type.id()==ID_rational)
    smt1_prop.out << "Real";
  else if(type.id()==ID_integer)
    smt1_prop.out << "Int";
  else if(type.id()==ID_symbol)
    convert_type(ns.follow(type));
  else
    throw "unsupported type: "+type.id_string();
}

/*******************************************************************\

Function: smt1_convt::from_bv_begin

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::from_bv_begin(const typet &type, bool bool_as_bv)
{
  // this turns bv[1] into a predicate if needed
  if(type.id()==ID_bool && !bool_as_bv)
    smt1_prop.out << "(= ";
}

/*******************************************************************\

Function: smt1_convt::from_bv_end

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::from_bv_end(const typet &type, bool bool_as_bv)
{
  // this turns bv[1] into a predicate if needed
  if(type.id()==ID_bool && !bool_as_bv)
    smt1_prop.out << " bv1[1])";
}

/*******************************************************************\

Function: smt1_convt::from_bool_begin

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::from_bool_begin(const typet &type, bool bool_as_bv)
{
  // this turns a predicate into bv[1] if needed
  if(type.id()==ID_bool && bool_as_bv)
    smt1_prop.out << "(ite ";
}

/*******************************************************************\

Function: smt1_convt::from_bool_end

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::from_bool_end(const typet &type, bool bool_as_bv)
{
  // this turns a predicate into bv[1] if needed
  if(type.id()==ID_bool && bool_as_bv)
    smt1_prop.out << " bv1[1] bv0[1])";
}

/*******************************************************************\

Function: smt1_convt::find_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::find_symbols(const typet &type)
{
  std::set<irep_idt> rec_stack;
  find_symbols_rec(type, rec_stack);
}

/*******************************************************************\

Function: smt1_convt::find_symbols_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::find_symbols_rec(
  const typet &type, 
  std::set<irep_idt> &recstack)
{
  if(type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(type);
    find_symbols(array_type.size());
    find_symbols_rec(array_type.subtype(), recstack);
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union)
  {
    const struct_union_typet::componentst &components=
      to_struct_union_type(type).components();

    for(unsigned i=0; i<components.size(); i++)
      find_symbols_rec(components[i].type(), recstack);
  }
  else if(type.id()==ID_code)
  {
    const code_typet::argumentst &arguments=
      to_code_type(type).arguments();

    for(unsigned i=0; i<arguments.size(); i++)
      find_symbols_rec(arguments[i].type(), recstack);

    find_symbols_rec(to_code_type(type).return_type(), recstack);
  }
  else if(type.id()==ID_pointer)
  {
    find_symbols_rec(type.subtype(), recstack);
  }
  else if(type.id()==ID_incomplete_array)
  {
    find_symbols_rec(type.subtype(), recstack);
  }
  else if(type.id()==ID_symbol)
  {
    const symbol_typet &st=to_symbol_type(type);
    const irep_idt &id=st.get_identifier();
    
    if(recstack.find(id)==recstack.end())
    {
      recstack.insert(id);
      find_symbols_rec(ns.follow(type), recstack);
    }
  }
}

/*******************************************************************\

Function: smt1_convt::binary2struct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt smt1_convt::binary2struct(
  const struct_typet &type,
  const std::string &binary) const
{
  const struct_typet::componentst &components=type.components();

  // std::cout << "S: " << stype << std::endl;

  unsigned total_width=boolbv_width(type);

  if(total_width==0)
    throw "failed to get struct width";

  // std::cout << "B: " << binary << std::endl;

  exprt e(type.id(), type);

  unsigned inx=binary.size();
  for(unsigned i=0; i<components.size(); i++)
  {
    const struct_union_typet::componentt &comp=components[i];

    unsigned sub_size=boolbv_width(comp.type());
    
    if(sub_size==0)
      throw "failed to get component width";

    inx-=sub_size;
    std::string cval=binary.substr(inx, sub_size);
    // std::cout << "CV[" << sub_size << "]: " << cval << std::endl;

    if(comp.type().id()==ID_struct)
    {
      exprt c=binary2struct(to_struct_type(comp.type()), cval);
      e.move_to_operands(c);
    }
    else if(comp.type().id()==ID_union)
    {
      exprt c=binary2union(to_union_type(comp.type()), cval);
      e.move_to_operands(c);
    }
    else
    {
      constant_exprt c(comp.type());
      c.set_value(cval);
      e.move_to_operands(c);
    }
  }

  return e;
}

/*******************************************************************\

Function: smt1_convt::binary2union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt smt1_convt::binary2union(
  const union_typet &type,
  const std::string &binary) const
{
  const union_typet::componentst &components=type.components();

  // std::cout << "S: " << stype << std::endl;

  unsigned total_width=boolbv_width(type);

  if(total_width==0)
    throw "failed to get union width";

  // std::cout << "B: " << binary << std::endl;

  exprt e(type.id(), type);

  // todo
  return nil_exprt();  
}

/*******************************************************************\

Function: smt1_convt::flatten_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::flatten_array(const exprt &op)
{
  const array_typet array_type=to_array_type(op.type());
  const typet &elem_type=array_type.subtype();
  const exprt &size=array_type.size();

  if(size.id()!="constant")
    throw ("non-constant size array cannot be flattened.");

  mp_integer sizei;
  if(to_integer(size, sizei))
    throw "array with non-constant size";

  unsigned elem_width=boolbv_width(elem_type);
  
  if(elem_width==0)
    throw "failed to get width of array subtype";

  #if 0
  smt1_prop.out << " (let (?fbv ";
  convert_expr(op, true);
  smt1_prop.out << ")";
  #endif

  for(mp_integer i=1; i<sizei; ++i)
    smt1_prop.out << "(concat ";

  for(mp_integer i=0; i<sizei; ++i)
  {
    smt1_prop.out << " (select ";
    #if 0
    smt1_prop.out << "?fbv";
    #else
    convert_expr(op, true);
    #endif
    smt1_prop.out << " ";
    smt1_prop.out << "bv" << i << "[" << array_index_bits << "]";
    smt1_prop.out << ")";
    if(i!=0) smt1_prop.out << ")"; // concat
  }

  #if 0
  smt1_prop.out << ")"; // let
  #endif
}

/*******************************************************************\

Function: smt1_convt::convert_nary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt1_convt::convert_nary(
  const exprt &expr,
  const irep_idt op_string,
  bool bool_as_bv)
{
  unsigned num_ops=expr.operands().size();

  assert(num_ops > 0);

  if(num_ops==1)
    convert_expr(expr.op0(), bool_as_bv);
  else
  {
    exprt::operandst::const_iterator it=expr.operands().begin();

    for(unsigned i=0; i<num_ops-1; ++i, ++it)
    {
      smt1_prop.out << " (" << op_string << " ";
      convert_expr(*it, bool_as_bv);
    }

    smt1_prop.out << " ";
    convert_expr(*it, bool_as_bv);

    // do the many closing parentheses
    smt1_prop.out << std::string (num_ops-1, ')');
  }
}
