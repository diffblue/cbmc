/*******************************************************************\

Module: SMT Backend

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <arith_tools.h>
#include <expr_util.h>
#include <std_types.h>
#include <std_expr.h>
#include <i2string.h>
#include <fixedbv.h>
#include <pointer_offset_size.h>
#include <ieee_float.h>

#include <ansi-c/string_constant.h>

#include <langapi/language_util.h>

#include <solvers/flattening/boolbv_width.h>

#include "smt2_conv.h"

/*******************************************************************\

Function: smt2_convt::dec_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt smt2_convt::dec_solve()
{
  smt2_prop.finalize();
  return decision_proceduret::D_ERROR;
}

/*******************************************************************\

Function: smt2_convt::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt smt2_convt::get(const exprt &expr) const
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

Function: smt2_convt::set_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::set_value(
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
    assert(v.size()==boolbv_width(type));
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
    // TODO
    assert(v.size()==boolbv_width(type));

    pointer_logict::pointert p;
    p.object=integer2long(binary2integer(std::string(v, 0, BV_ADDR_BITS), false));
    p.offset=binary2integer(std::string(v, BV_ADDR_BITS, std::string::npos), true);

    identifier.value=pointer_logic.pointer_expr(p, type);
  }
  else if(type.id()==ID_struct)
  {
    // TODO
  }
  else if(type.id()==ID_union)
  {
    // TODO
  }
}

/*******************************************************************\

Function: smt2_convt::array_index_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet smt2_convt::array_index_type() const
{
  signedbv_typet t;
  t.set_width(array_index_bits);
  return t;
}

/*******************************************************************\

Function: smt2_convt::array_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::array_index(const exprt &expr)
{
  typet t=array_index_type();
  if(t==expr.type()) return convert_expr(expr);
  typecast_exprt tmp(t);
  tmp.op0()=expr;
  convert_expr(tmp);
}

/*******************************************************************\

Function: smt2_convt::convert_address_of_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_address_of_rec(
  const exprt &expr,
  const pointer_typet &result_type)
{
  if(expr.id()==ID_symbol ||
     expr.id()==ID_constant ||
     expr.id()==ID_string_constant ||
     expr.id()==ID_label)
  {
    smt2_prop.out
      << "(concat (_ bv"
      << pointer_logic.add_object(expr) << " " << BV_ADDR_BITS << ")"
      << " (_ bv0 " << boolbv_width(result_type)-BV_ADDR_BITS << "))";
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
        convert_expr(array);
      else if(array.type().id()==ID_array)
        convert_address_of_rec(array, result_type);
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

      convert_expr(plus_expr);
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
      index_type.set(ID_width, boolbv_width(result_type));

      // pointer arithmetic
      smt2_prop.out << "(bvadd ";
      convert_address_of_rec(struct_op, result_type);
      convert_expr(from_integer(offset, index_type));
      smt2_prop.out << ")"; // bvadd
    }
    else
      throw "unexpected type of member operand";

  }
  else if(expr.id()==ID_if)
  {
    assert(expr.operands().size()==3);

    smt2_prop.out << "(ite ";
    convert_expr(expr.op0());
    smt2_prop.out << " ";
    convert_address_of_rec(expr.op1(), result_type);
    smt2_prop.out << " ";
    convert_address_of_rec(expr.op2(), result_type);
    smt2_prop.out << ")";
  }
  else
    throw "don't know how to take address of: "+expr.id_string();
}

/*******************************************************************\

Function: smt2_convt::convert_byte_extract

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_byte_extract(const exprt &expr)
{
  mp_integer i;
  if(to_integer(expr.op1(), i))
    throw "byte_extract takes constant as second parameter";

  boolbv_widtht boolbv_width(ns);
  
  unsigned w=boolbv_width(expr.op0().type());
  if(w==0)
    throw "failed to get width of byte_extract operand";

  smt2_prop.out << "";

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

  smt2_prop.out << "((_ extract " << upper << " " << lower << ") ";
  convert_expr(expr.op0());
  smt2_prop.out << ")";
}

/*******************************************************************\

Function: smt2_convt::convert_byte_update

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_byte_update(const exprt &expr)
{
  assert(expr.operands().size()==3);

  // The situation: expr.op0 needs to be split in 3 parts
  // |<--- L --->|<--- M --->|<--- R --->|
  // where M is the expr.op1'th byte
  // We need to output L expr.op2 R

  mp_integer i;
  if(to_integer(expr.op1(), i))
    throw "byte_extract takes constant as second parameter";

  boolbv_widtht boolbv_width(ns);
  
  unsigned w=boolbv_width(expr.op0().type());

  if(w==0)
    throw "failed to get width of byte_extract operand";

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
      convert_expr(expr.op2());
    else // uppermost byte selected, only R needed
    {
      smt2_prop.out << "(concat ";
      convert_expr(expr.op2());
      smt2_prop.out << " ((_ extract " << lower-1 << " 0) ";
      convert_expr(expr.op0());
      smt2_prop.out << "))";
    }
  }
  else
  {
    if(lower==0) // lowermost byte selected, only L needed
    {
      smt2_prop.out << "(concat ";
      smt2_prop.out << "((_ extract " << max << " " << (upper+1) << ") ";
      convert_expr(expr.op0());
      smt2_prop.out << ") ";
      convert_expr(expr.op2());
      smt2_prop.out << ")";
    }
    else // byte in the middle selected, L & R needed
    {
      smt2_prop.out << "(concat (concat ";
      smt2_prop.out << "((_ extract " << max << " " << (upper+1) << ") ";
      convert_expr(expr.op0());
      smt2_prop.out << ") ";
      convert_expr(expr.op2());
      smt2_prop.out << ") ((_ extract " << (lower-1) << " 0) ";
      convert_expr(expr.op0());
      smt2_prop.out << "))";
    }
  }

}

/*******************************************************************\

Function: smt2_convt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt smt2_convt::convert(const exprt &expr)
{
  assert(expr.type().id()==ID_bool);

  if(expr.is_true())
    return const_literal(true);
  else if(expr.is_false())
    return const_literal(false);

  smt2_prop.out << std::endl;

  find_symbols(expr);

  literalt l=smt2_prop.define_new_variable();
  smt2_prop.out << "; convert " << std::endl
                << " ";
  convert_expr(expr);
  smt2_prop.out << ")" << std::endl;

  return l;
}

/*******************************************************************\

Function: smt2_convt::convert_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string smt2_convt::convert_identifier(const irep_idt &identifier)
{
  // TODO: need to search for '|' in there
  std::string result="|"+id2string(identifier)+"|";
  return result;
}

/*******************************************************************\

Function: smt2_convt::convert_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_expr(const exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    irep_idt id=to_symbol_expr(expr).get_identifier();
    assert(id!="");

    smt2_prop.out << convert_identifier(id);
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    irep_idt id=expr.get(ID_identifier);
    assert(id!="");

    smt2_prop.out << "nondet_" << convert_identifier(id);
  }
  else if(expr.id()==ID_typecast)
  {
    convert_typecast(to_typecast_expr(expr));
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
    convert_constant(to_constant_expr(expr));
  }
  else if(expr.id()==ID_concatenation ||
          expr.id()==ID_bitand ||
          expr.id()==ID_bitor ||
          expr.id()==ID_bitxor ||
          expr.id()==ID_bitnand ||
          expr.id()==ID_bitnor)
  {
    assert(expr.operands().size()>=2);

    smt2_prop.out << "(";

    if(expr.id()==ID_concatenation)
      smt2_prop.out << "concat";
    else if(expr.id()==ID_bitand)
      smt2_prop.out << "bvand";
    else if(expr.id()==ID_bitor)
      smt2_prop.out << "bvor";
    else if(expr.id()==ID_bitxor)
      smt2_prop.out << "bvxor";
    else if(expr.id()==ID_bitnand)
      smt2_prop.out << "bvnand";
    else if(expr.id()==ID_bitnor)
      smt2_prop.out << "bvnor";

    forall_operands(it, expr)
    {
      smt2_prop.out << " ";
      convert_expr(*it);
    }

    smt2_prop.out << ")";
  }
  else if(expr.id()==ID_bitnot)
  {
    assert(expr.operands().size()==1);
    smt2_prop.out << "(bvnot ";
    convert_expr(expr.op0());
    smt2_prop.out << ")";
  }
  else if(expr.id()==ID_unary_minus)
  {
    assert(expr.operands().size()==1);

    if(expr.type().id()==ID_rational)
    {
      smt2_prop.out << "(- ";
      convert_expr(expr.op0());
      smt2_prop.out << ")";
    }
    else if(expr.type().id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
        smt2_prop.out << "(- "; // no rounding
        convert_expr(expr.op0());
        smt2_prop.out << ")";
      }
      else
      {
        throw "TODO: unary minus for floatbv";
      }
    }
    else
    {
      smt2_prop.out << "(bvneg ";
      convert_expr(expr.op0());
      smt2_prop.out << ")";
    }
  }
  else if(expr.id()==ID_if)
  {
    assert(expr.operands().size()==3);

    smt2_prop.out << "(ite ";
    convert_expr(expr.op0());
    smt2_prop.out << " ";
    convert_expr(expr.op1());
    smt2_prop.out << " ";
    convert_expr(expr.op2());
    smt2_prop.out << ")";
  }
  else if(expr.id()==ID_and ||
          expr.id()==ID_or ||
          expr.id()==ID_xor)
  {
    assert(expr.type().id()==ID_bool);
    assert(expr.operands().size()>=2);

    if(expr.operands().size()>=2)
    {
      smt2_prop.out << "(" << expr.id();
      forall_operands(it, expr)
      {
        smt2_prop.out << " ";
        convert_expr(*it);
      }
      smt2_prop.out << ")";
    }
    else
      assert(false);
  }
  else if(expr.id()==ID_implies)
  {
    assert(expr.type().id()==ID_bool);
    assert(expr.operands().size()==2);

    smt2_prop.out << "(implies ";
    convert_expr(expr.op0());
    smt2_prop.out << " ";
    convert_expr(expr.op1());
    smt2_prop.out << ")";
  }
  else if(expr.id()==ID_not)
  {
    assert(expr.type().id()==ID_bool);
    assert(expr.operands().size()==1);

    smt2_prop.out << "(not ";
    convert_expr(expr.op0());
    smt2_prop.out << ")";
  }
  else if(expr.id()==ID_equal ||
          expr.id()==ID_notequal)
  {
    assert(expr.operands().size()==2);
    assert(expr.op0().type()==expr.op1().type());

    if(expr.id()==ID_notequal)
    {
      smt2_prop.out << "(not (= ";
      convert_expr(expr.op0());
      smt2_prop.out << " ";
      convert_expr(expr.op1());
      smt2_prop.out << "))";
    }
    else
    {
      smt2_prop.out << "(= ";
      convert_expr(expr.op0());
      smt2_prop.out << " ";
      convert_expr(expr.op1());
      smt2_prop.out << ")";
    }
  }
  else if(expr.id()==ID_ieee_float_equal ||
          expr.id()==ID_ieee_float_notequal)
  {
    assert(expr.operands().size()==2);
    assert(expr.op0().type()==expr.op1().type());

    // These are not the same as (= A B)!

    if(use_FPA_theory)
    {
      if(expr.id()==ID_ieee_float_notequal)
      {
        smt2_prop.out << "(not (== ";
        convert_expr(expr.op0());
        smt2_prop.out << " ";
        convert_expr(expr.op1());
        smt2_prop.out << "))";
      }
      else
      {
        smt2_prop.out << "(== ";
        convert_expr(expr.op0());
        smt2_prop.out << " ";
        convert_expr(expr.op1());
        smt2_prop.out << ")";
      }
    }
    else
    {
      // TODO: NAN check!
      if(expr.id()==ID_ieee_float_notequal)
      {
        smt2_prop.out << "(not (= ";
        convert_expr(expr.op0());
        smt2_prop.out << " ";
        convert_expr(expr.op1());
        smt2_prop.out << "))";
      }
      else
      {
        smt2_prop.out << "(= ";
        convert_expr(expr.op0());
        smt2_prop.out << " ";
        convert_expr(expr.op1());
        smt2_prop.out << ")";
      }
    }
  }
  else if(expr.id()==ID_le ||
          expr.id()==ID_lt ||
          expr.id()==ID_ge ||
          expr.id()==ID_gt)
  {
    convert_relation(expr);
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
    convert_address_of_rec(expr.op0(), to_pointer_type(expr.type()));
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

    smt2_prop.out << it->second;
  }
  else if(expr.id()==ID_index)
  {
    convert_index(to_index_expr(expr));
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
        smt2_prop.out << "(bvashr ";
      else if(expr.id()==ID_lshr)
        smt2_prop.out << "(bvlshr ";
      else if(expr.id()==ID_shl)
        smt2_prop.out << "(bvshl ";
      else
        assert(false);

      convert_expr(expr.op0());
      smt2_prop.out << " ";
      convert_expr(expr.op1());
      smt2_prop.out << ")";
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
    convert_member(to_member_expr(expr));
  }
  else if(expr.id()==ID_pointer_offset)
  {
    assert(expr.operands().size()==1);
    assert(expr.op0().type().id()==ID_pointer);
    unsigned offset_bits=boolbv_width(expr.op0().type())-BV_ADDR_BITS;
    unsigned result_width=boolbv_width(expr.type());

    // max extract width    
    if(offset_bits>result_width) offset_bits=result_width;
    
    // too few bits?
    if(result_width>offset_bits)
      smt2_prop.out << "((_ zero_extend " << result_width-offset_bits << ") ";
    
    smt2_prop.out << "((_ extract " << offset_bits-1 << " 0) ";
    convert_expr(expr.op0());
    smt2_prop.out << ")";

    if(result_width>offset_bits)
      smt2_prop.out << ")"; // zero_extend
  }
  else if(expr.id()==ID_pointer_object)
  {
    assert(expr.operands().size()==1);
    assert(expr.op0().type().id()==ID_pointer);
    unsigned ext=boolbv_width(expr.type())-BV_ADDR_BITS;
    unsigned pointer_width=boolbv_width(expr.op0().type());

    if(ext>0)
      smt2_prop.out << "((_ zero_extend " << ext << ") ";

    smt2_prop.out << "((_ extract "
                  << pointer_width-1 << " "
                  << pointer_width-BV_ADDR_BITS << ") ";
    convert_expr(expr.op0());
    smt2_prop.out << ")";

    if(ext>0)
      smt2_prop.out << ")"; // zero_extend
  }
  else if(expr.id()=="same-object")
  {
    assert(expr.operands().size()==2);
    unsigned pointer_width0=boolbv_width(expr.op0().type());
    unsigned pointer_width1=boolbv_width(expr.op1().type());

    smt2_prop.out << "(= ((_ extract " << pointer_width0-1
                  << " " << pointer_width0-BV_ADDR_BITS << ") ";
    convert_expr(expr.op0());
    smt2_prop.out << ")";

    smt2_prop.out << " ((_ extract " << pointer_width1-1
                  << " " << pointer_width1-BV_ADDR_BITS << ") ";
    convert_expr(expr.op1());
    smt2_prop.out << "))";
  }
  else if(expr.id()=="is_dynamic_object")
  {
    convert_is_dynamic_object(expr);
  }
  else if(expr.id()=="invalid-pointer")
  {
    assert(expr.operands().size()==1);

    unsigned pointer_width=boolbv_width(expr.op0().type());
    smt2_prop.out << "(= ((_ extract "
                  << pointer_width-1 << " "
                  << pointer_width-BV_ADDR_BITS << ") ";
    convert_expr(expr.op0());
    smt2_prop.out << ") (_ bv" << pointer_logic.get_invalid_object()
                  << " " << BV_ADDR_BITS << "))";
  }
  else if(expr.id()=="pointer_object_has_type")
  {
    assert(expr.operands().size()==1);

    smt2_prop.out << "false"; // TODO
  }
  else if(expr.id()==ID_string_constant)
  {
    exprt tmp;
    string2array_mapt::const_iterator fit=string2array_map.find(expr);
    assert(fit!=string2array_map.end());

    convert_expr(fit->second);
  }
  else if(expr.id()==ID_extractbit)
  {
    assert(expr.operands().size()==2);

    if(expr.op0().type().id()==ID_unsignedbv ||
       expr.op0().type().id()==ID_signedbv ||
       expr.op0().type().id()==ID_bv ||
       expr.op0().type().id()==ID_fixedbv)
    {
      if(expr.op1().is_constant())
      {
        mp_integer i;
        if(to_integer(expr.op1(), i))
          throw "extractbit: to_integer failed";

        smt2_prop.out << "(= ((_ extract " << i << " " << i << ") ";
        convert_expr(expr.op0());
        smt2_prop.out << ") bit1)";
      }
      else
      {
        smt2_prop.out << "(= ((_ extract 0 0) ";
        // the arguments of the shift need to have the same width
        smt2_prop.out << "(bvlshr ";
        convert_expr(expr.op0());
        typecast_exprt tmp(expr.op0().type());
        tmp.op0()=expr.op1();
        convert_expr(tmp);
        smt2_prop.out << ")) bin1)"; // bvlshr, extract, =
      }
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

    smt2_prop.out << "((_ repeat " << times << ") ";
    // todo: need to deal with boolean
    convert_expr(expr.op1());
    smt2_prop.out << ")";
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
    boolbv_widtht boolbv_width(ns);
  
    unsigned result_width=boolbv_width(expr.type());
    
    if(result_width==0)
      throw "conversion failed";

    if(expr.operands().size()!=1)
      throw "width expects 1 operand";

    unsigned op_width=boolbv_width(expr.op0().type());
    
    if(op_width==0)
      throw "conversion failed";

    smt2_prop.out << "(_ bv" << op_width/8
                  << " " << result_width << ")";
  }
  else if(expr.id()==ID_abs)
  {
    assert(expr.operands().size()==1);

    const typet &type=expr.type();

    if(type.id()==ID_signedbv)
    {
      unsigned result_width=to_signedbv_type(type).get_width();
            
      smt2_prop.out << "(ite (bvslt ";
      convert_expr(expr.op0());
      smt2_prop.out << " (_ bv0 " << result_width << ")) ";
      smt2_prop.out << "(bvneg ";
      convert_expr(expr.op0());
      smt2_prop.out << ") ";
      convert_expr(expr.op0());
      smt2_prop.out << ")";
    }
    else if(type.id()==ID_fixedbv)
    {
      unsigned result_width=to_fixedbv_type(type).get_width();
      
      smt2_prop.out << "(ite (bvslt ";
      convert_expr(expr.op0());
      smt2_prop.out << " (_ bv0 " << result_width << ")) ";
      smt2_prop.out << "(bvneg ";
      convert_expr(expr.op0());
      smt2_prop.out << ") ";
      convert_expr(expr.op0());
      smt2_prop.out << ")";
    }
    else if(type.id()==ID_floatbv)
    {
      const floatbv_typet &floatbv_type=to_floatbv_type(type);

      if(use_FPA_theory)
      {
        smt2_prop.out << "(abs (_ FP "
                      << floatbv_type.get_e() << " "
                      << floatbv_type.get_f() << ") ";
        convert_expr(expr.op0());
        smt2_prop.out << ")";
      }
      else
      {
        // bit-level encoding
        unsigned result_width=floatbv_type.get_width();
        smt2_prop.out << "(bvand ";
        convert_expr(expr.op0());
        smt2_prop.out << " (_ bv"
                      << (power(2, result_width-1)-1)
                      << " " << result_width << "))";
      }
    }
    else
      throw "abs with unsupported operand type";
  }
  else if(expr.id()==ID_isnan)
  {
    assert(expr.operands().size()==1);

    const typet &op_type=expr.op0().type();

    if(op_type.id()==ID_fixedbv)
      smt2_prop.out << "false";
    else if(op_type.id()==ID_floatbv)
    {
      const floatbv_typet &floatbv_type=to_floatbv_type(op_type);
      if(use_FPA_theory)
      {
        smt2_prop.out << "(isNaN ";
        convert(expr.op0());
        smt2_prop.out << floatbv_type.get_f() << ")";
      }
      else
      {
        throw "TODO: isNaN for flaotbv";
      }
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
      smt2_prop.out << "true";
    else if(op_type.id()==ID_floatbv)
    {
      const floatbv_typet &floatbv_type=to_floatbv_type(op_type);
      if(use_FPA_theory)
      {
        smt2_prop.out << "(isFinite ";
        convert(expr.op0());
        smt2_prop.out << floatbv_type.get_f() << ")";
      }
      else
      {
        throw "TODO: isfinite for floatbv";
      }
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
      smt2_prop.out << "false";
    else if(op_type.id()==ID_floatbv)
    {
      const floatbv_typet &floatbv_type=to_floatbv_type(op_type);
      if(use_FPA_theory)
      {
        smt2_prop.out << "(not (isFinite ";
        convert(expr.op0());
        smt2_prop.out << floatbv_type.get_f() << "))";
      }
      else
      {
        throw "TODO: isinf for floatbv";
      }
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
      smt2_prop.out << "true";
    else if(op_type.id()==ID_floatbv)
    {
      const floatbv_typet &floatbv_type=to_floatbv_type(op_type);
      if(use_FPA_theory)
      {
        smt2_prop.out << "(isNormal ";
        convert(expr.op0());
        smt2_prop.out << floatbv_type.get_f() << ")";
      }
      else
      {
        throw "TODO: isNormal for floatbv";
      }
    }
    else
      throw "isnormal with unsupported operand type";
  }
  else if(expr.id()=="overflow-+" ||
          expr.id()=="overflow--")
  {
    assert(expr.operands().size()==2);
    assert(expr.type().id()==ID_bool);

    bool subtract=expr.id()=="overflow--";
    const typet &op_type=expr.op0().type();
    unsigned width=boolbv_width(op_type);

    if(op_type.id()==ID_signedbv)
    {
      // an overflow occurs if the top two bits of the extended sum differ
      smt2_prop.out << "(let ((?sum (";
      smt2_prop.out << (subtract?"bvsub":"bvadd");
      smt2_prop.out << " ((_ sign_extend 1) ";
      convert_expr(expr.op0());
      smt2_prop.out << ")";
      smt2_prop.out << " ((_ sign_extend 1) ";
      convert_expr(expr.op1());
      smt2_prop.out << ")))) "; // sign_extend, bvadd/sub let2
      smt2_prop.out << "(not (= "
                      "((_ extract " << width << " " << width << ") ?sum) "
                      "((_ extract " << (width-1) << " " << (width-1) << ") ?sum)";
      smt2_prop.out << ")))"; // =, not, let
    }
    else if(op_type.id()==ID_unsignedbv)
    {
      // overflow is simply carry-out
      smt2_prop.out << "(= ";
      smt2_prop.out << "((_ extract " << width << " " << width << ") ";
      smt2_prop.out << "(" << (subtract?"bvsub":"bvadd");
      smt2_prop.out << " ((_ zero_extend 1) ";
      convert_expr(expr.op0());
      smt2_prop.out << ")";
      smt2_prop.out << " ((_ zero_extend 1) ";
      convert_expr(expr.op1());
      smt2_prop.out << ")))"; // zero_extend, bvsub/bvadd, extract
      smt2_prop.out << " bit1)"; // =
    }
    else
      throw "overflow check on unknown type: "+op_type.id_string();
  }
  else if(expr.id()=="overflow-*")
  {
    assert(expr.operands().size()==2);
    throw "not yet implemented: overflow-*";
  }
  else
    throw "smt2_convt::convert_expr: `"+
          expr.id_string()+"' is unsupported";
}

/*******************************************************************\

Function: smt2_convt::convert_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_typecast(const typecast_exprt &expr)
{
  assert(expr.operands().size()==1);
  const exprt &op=expr.op0();
  const typet &expr_type=ns.follow(expr.type());
  const typet &op_type=ns.follow(op.type());

  if(expr_type.id()==ID_bool)
  {
    // this is comparison with zero
    if(op_type.id()==ID_signedbv ||
       op_type.id()==ID_unsignedbv ||
       op_type.id()==ID_fixedbv ||
       op_type.id()==ID_pointer)
    {
      smt2_prop.out << "(not (= ";
      convert_expr(op);
      smt2_prop.out << " ";
      convert_expr(gen_zero(op_type));
      smt2_prop.out << "))";
    }
    else
    {
      throw "TODO typecast1 "+op_type.id_string()+" -> bool";
    }
  }
  else if(expr_type.id()==ID_signedbv ||
          expr_type.id()==ID_unsignedbv ||
          expr_type.id()==ID_c_enum)
  {
    unsigned to_width=boolbv_width(expr_type);

    if(op_type.id()==ID_signedbv || // from signedbv
       op_type.id()==ID_unsignedbv || // from unsigedbv
       op_type.id()==ID_c_enum)
    {
      unsigned from_width=boolbv_width(op_type);

      if(from_width==to_width)
        convert_expr(op); // ignore
      else if(from_width<to_width) // extend
      {
        if(op_type.id()==ID_signedbv)
          smt2_prop.out << "((_ sign_extend ";
        else
          smt2_prop.out << "((_ zero_extend";

        smt2_prop.out << (to_width-from_width)
                      << ") "; // ind
        convert_expr(op);
        smt2_prop.out << ")";
      }
      else // chop off extra bits
      {
        smt2_prop.out << "((_ extract " << (to_width-1) << " 0) ";
        convert_expr(op);
        smt2_prop.out << ")";
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
        smt2_prop.out << "((_ sign_extend "
                      << (to_width-from_integer_bits) << ") ";
        smt2_prop.out << "((_ extract " << (from_width-1) << " "
                      << from_fraction_bits << ") ";
        convert_expr(op);
        smt2_prop.out << "))";
      }
      else
      {
        smt2_prop.out << "((_ extract " << (from_fraction_bits+to_width-1)
                      << " " << from_fraction_bits << ") ";
        convert_expr(op);
        smt2_prop.out << ")";
      }
    }
    else if(op_type.id()==ID_bool) // from boolean
    {
      smt2_prop.out << "(ite ";
      convert_expr(op);

      if(expr_type.id()==ID_fixedbv)
      {
        fixedbvt fbt(expr);
        smt2_prop.out << " (concat (_ bv1 "
                      << fbt.spec.integer_bits << ") " <<
                         "(_ bv0 " << fbt.spec.get_fraction_bits() << ")) " <<
                         "(_ bv0 " << fbt.spec.width << ")";
      }
      else
      {
        smt2_prop.out << " (_ bv1 " << to_width << ")";
        smt2_prop.out << " (_ bv0 " << to_width << ")";
      }

      smt2_prop.out << ")";
    }
    else if(op_type.id()==ID_pointer) // from pointer to int
    {
      unsigned from_width=boolbv_width(op_type);

      if(from_width<to_width) // extend
      {
        smt2_prop.out << "((_ sign_extend ";
        smt2_prop.out << (to_width-from_width)
                      << ") ";
        convert_expr(op);
        smt2_prop.out << ")";
      }
      else // chop off extra bits
      {
        smt2_prop.out << "((_ extract " << (to_width-1) << " 0) ";
        convert_expr(op);
        smt2_prop.out << ")";
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
      smt2_prop.out << "(concat ";

      if(from_width==to_integer_bits)
        convert_expr(op);
      else if(from_width>to_integer_bits)
      {
        smt2_prop.out << "((_ extract " << (to_integer_bits-1) << " "
                      << to_fraction_bits << ") ";
        convert_expr(op);
        smt2_prop.out << ")";
      }
      else
      {
        assert(from_width<to_integer_bits);
        if(expr_type.id()==ID_unsignedbv)
        {
          smt2_prop.out << "(_ zero_extend "
                        << (to_integer_bits-from_width) << ") ";
          convert_expr(op);
          smt2_prop.out << ")";
        }
        else
        {
          smt2_prop.out << "((_ sign_extend "
                        << (to_integer_bits-from_width) << ") ";
          convert_expr(op);
          smt2_prop.out << ")";
        }
      }

      smt2_prop.out << "(_ bv0 " << to_fraction_bits << ")";
      smt2_prop.out << ")"; // concat
    }
    else if(op_type.id()==ID_bool)
    {
      smt2_prop.out << "(concat (concat"
                    << " (_ bv0 " << (to_integer_bits-1) << ")"
                    << " (ite ";
      convert_expr(op); // this returns a Bool
      smt2_prop.out << " bit1 bit0)) (_ bv0 "
                    << to_fraction_bits
                    << "))";
    }
    else if(op_type.id()==ID_fixedbv)
    {
      const fixedbv_typet &from_fixedbv_type=to_fixedbv_type(op_type);
      unsigned from_fraction_bits=from_fixedbv_type.get_fraction_bits();
      unsigned from_integer_bits=from_fixedbv_type.get_integer_bits();
      unsigned from_width=from_fixedbv_type.get_width();

      // TODO: use let for op
      smt2_prop.out << "(concat ";

      if(to_integer_bits<=from_integer_bits)
      {
        smt2_prop.out << "((_ extract "
                      << (from_fraction_bits+to_integer_bits-1) << " "
                      << from_fraction_bits
                      << ") ";
        convert_expr(op);
        smt2_prop.out << ")";
      }
      else
      {
        assert(to_integer_bits>from_integer_bits);
        smt2_prop.out << "((_ sign_extend "
                      << (to_integer_bits-from_integer_bits)
                      << ") ((_ extract "
                      << (from_width-1) << " "
                      << from_fraction_bits
                      << ") ";
        convert_expr(op);
        smt2_prop.out << "))";
      }

      smt2_prop.out << " ";

      if(to_fraction_bits<=from_fraction_bits)
      {
        smt2_prop.out << "((_ extract "
                      << (from_fraction_bits-1) << " "
                      << (from_fraction_bits-to_fraction_bits)
                      << ") ";
        convert_expr(op);
        smt2_prop.out << ")";
      }
      else
      {
        assert(to_fraction_bits>from_fraction_bits);
        smt2_prop.out << "(concat ((_ extract "
                      << (from_fraction_bits-1) << " 0) ";
        convert_expr(op);
        smt2_prop.out << ")"
                      << " (_ bv0 " << to_fraction_bits-from_fraction_bits
                      << "))";
      }

      smt2_prop.out << ")"; // concat
    }
    else
      throw "unexpected typecast to fixedbv";
  }
  else if(expr_type.id()==ID_pointer)
  {
    unsigned to_width=boolbv_width(expr_type);
  
    if(op_type.id()==ID_pointer)
    {
      // this just passes through
      convert_expr(op);
    }
    else if(op_type.id()==ID_unsigned ||
            op_type.id()==ID_signedbv)
    {
      // integer to pointer
    
      unsigned from_width=boolbv_width(op_type);

      if(from_width==to_width)
        convert_expr(op);
      else if(from_width<to_width)
      {
        smt2_prop.out << "((_ sign_extend "
                      << (to_width-from_width)
                      << ") ";
        convert_expr(op);
        smt2_prop.out << ")"; // sign_extend
      }
      else // from_width>to_width
      {
        smt2_prop.out << "((_ extract " << to_width << " 0) ";
        convert_expr(op);
        smt2_prop.out << ")"; // extract
      }
    }
    else
      throw "TODO typecast3 "+op_type.id_string()+" -> pointer";
  }
  else if(expr_type.id()==ID_range)
  {
    throw "TODO range typecast";
  }
  else if(expr_type.id()==ID_floatbv)
  {
    if(op_type.id()==ID_floatbv)
    {
//      const floatbv_typet &src=to_floatbv_type(op_type);
      const floatbv_typet &dst=to_floatbv_type(expr_type);

      if(use_FPA_theory)
      {
        smt2_prop.out << "((_ cast " << dst.get_e() << " "
                      << dst.get_f() << ") (RNE (";
        convert_expr(op);
        smt2_prop.out << "))";
      }
      else
      {
        throw "TODO typecast4 floatbv -> floatbv";
      }
    }
    else
      throw "TODO typecast5 floatbv -> "+op_type.id_string();
  }
  else
    throw "TODO typecast6 "+op_type.id_string()+" -> "+expr_type.id_string();
}

/*******************************************************************\

Function: smt2_convt::convert_struct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_struct(const exprt &expr)
{
  const struct_typet &struct_type=to_struct_type(expr.type());

  const struct_typet::componentst &components=
    struct_type.components();

  assert(components.size()==expr.operands().size());

  assert(!components.empty());

  if(components.size()==1)
    convert_expr(expr.op0());
  else
  {
    smt2_prop.out << "(concat";
    unsigned i=0;
    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++, i++)
    {
      if(it->type().id()!=ID_code)
      {
        smt2_prop.out << " ";
        //const exprt &op=expr.operands()[i];

        #if 0
        if(op.type().id()==ID_array)
          flatten_array(op);
        else
          convert_expr(op);
        #endif
        // TODO
      }
    }

    smt2_prop.out << ")";
  }
}

/*******************************************************************\

Function: smt2_convt::convert_union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_union(const exprt &expr)
{
  const union_typet &union_type=to_union_type(expr.type());

  assert(expr.operands().size()==1);
  const exprt &op=expr.op0();

  boolbv_widtht boolbv_width(ns);

  unsigned total_width=boolbv_width(union_type);

  if(total_width==0)
    throw "failed to get union width for union";

  unsigned member_width=boolbv_width(op.type());

  if(member_width==0)
    throw "failed to get union member width for union";

  if(total_width==member_width)
  {
    // TODO: deal with boolean
    convert_expr(op);
  }
  else
  {
    // we will pad with zeros, but non-det would be better
    assert(total_width>member_width);
    smt2_prop.out << "(concat ";
    smt2_prop.out << "(_ bv0 "
                  << (total_width-member_width) << ") ";
    // TODO: deal with boolean
    convert_expr(op);
    smt2_prop.out << ")";
  }
}

/*******************************************************************\

Function: smt2_convt::convert_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_constant(const constant_exprt &expr)
{
  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv ||
     expr.type().id()==ID_bv ||
     expr.type().id()==ID_c_enum)
  {
    mp_integer value;

    if(to_integer(expr, value))
      throw "failed to convert bitvector constant";

    unsigned width=boolbv_width(expr.type());

    if(value<0) value=power(2, width)+value;

    smt2_prop.out << "(_ bv" << value
                  << " " << width << ")";
  }
  else if(expr.type().id()==ID_fixedbv)
  {
    fixedbv_spect spec(to_fixedbv_type(expr.type()));

    std::string v_str=id2string(expr.get(ID_value));
    mp_integer v=binary2integer(v_str, false);

    smt2_prop.out << "(_ bv" << v << " " << spec.width << ")";
  }
  else if(expr.type().id()==ID_floatbv)
  {
    const floatbv_typet &floatbv_type=
      to_floatbv_type(expr.type());
  
    if(use_FPA_theory)
    {
      ieee_floatt v=ieee_floatt(expr);
      smt2_prop.out << "((_ asFloat "
                    << floatbv_type.get_e() << " "
                    << floatbv_type.get_f() << ") "
                    << "(RNE " << v.get_sign() << " "
                    << v.get_fraction() << " "
                    << v.get_exponent() << "))";
    }
    else
    {
      // produce corresponding bit-vector
      ieee_float_spect spec(floatbv_type);

      std::string v_str=id2string(expr.get(ID_value));
      mp_integer v=binary2integer(v_str, false);

      smt2_prop.out << "(_ bv" << v << " " << spec.width() << ")";
    }
  }
  else if(expr.type().id()==ID_pointer)
  {
    const irep_idt &value=expr.get(ID_value);

    if(value==ID_NULL)
    {
      smt2_prop.out << "(_ bv0 " << boolbv_width(expr.type())
                    << ")";
    }
    else
      throw "unknown pointer constant: "+id2string(value);
  }
  else if(expr.type().id()==ID_bool)
  {
    if(expr.is_true())
      smt2_prop.out << "true";
    else if(expr.is_false())
      smt2_prop.out << "false";
    else
      throw "unknown boolean constant";
  }
  else if(expr.type().id()==ID_array)
  {
    array_init_mapt::const_iterator it=array_init_map.find(expr);
    assert(it!=array_init_map.end());

    std::string tmp;
    tmp = it->second.as_string();

    assert(expr.operands().size()!=0);

    forall_operands(it, expr)
      smt2_prop.out << "(store ";

    smt2_prop.out << it->second;

    unsigned i=0;
    forall_operands(it, expr)
    {
      exprt inx = from_integer(i, unsignedbv_typet(array_index_bits));
      smt2_prop.out << " ";
      convert_expr(inx);
      smt2_prop.out << " ";
      convert_expr(*it);
      smt2_prop.out << ")";
      i++;
    }
  }
  else if(expr.type().id()==ID_rational)
  {
    std::string value=expr.get(ID_value).as_string();
    size_t pos=value.find("/");

    if(pos==std::string::npos)
      smt2_prop.out << value << ".0";
    else
    {
      smt2_prop.out << "(/ " << value.substr(0,pos) << ".0 "
                             << value.substr(pos+1) << ".0)";
    }
  }
  else if(expr.type().id()==ID_integer)
  {
    smt2_prop.out << expr.get(ID_value);
  }
  else
    throw "unknown constant: "+expr.type().id_string();
}

/*******************************************************************\

Function: smt2_convt::convert_mod

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_mod(const exprt &expr)
{
  assert(expr.operands().size()==2);

  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv)
  {
    if(expr.type().id()==ID_unsignedbv)
      smt2_prop.out << "(bvurem ";
    else
      smt2_prop.out << "(bvsrem ";

    convert_expr(expr.op0());
    smt2_prop.out << " ";
    convert_expr(expr.op1());
    smt2_prop.out << ")";
  }
  else
    throw "unsupported type for mod: "+expr.type().id_string();
}

/*******************************************************************\

Function: smt2_convt::convert_is_dynamic_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_is_dynamic_object(const exprt &expr)
{
  std::vector<unsigned> dynamic_objects;
  pointer_logic.get_dynamic_objects(dynamic_objects);

  assert(expr.operands().size()==1);

  if(dynamic_objects.empty())
    smt2_prop.out << "false";
  else
  {
    unsigned pointer_width=boolbv_width(expr.op0().type());
  
    smt2_prop.out << "(let ((?obj ((_ extract " 
                  << pointer_width-1 << " "
                  << pointer_width-BV_ADDR_BITS << ") ";
    convert_expr(expr.op0());
    smt2_prop.out << "))) ";

    if(dynamic_objects.size()==1)
    {
      smt2_prop.out << "(= (_ bv" << dynamic_objects.front()
                    << " " << BV_ADDR_BITS << ") ?obj)";
    }
    else
    {
      smt2_prop.out << "(or";

      for(std::vector<unsigned>::const_iterator
          it=dynamic_objects.begin();
          it!=dynamic_objects.end();
          it++)
        smt2_prop.out << " (= (_ bv" << *it
                      << " " << BV_ADDR_BITS << ") ?obj)";

      smt2_prop.out << ")"; // or
    }

    smt2_prop.out << ")"; // let
  }
}

/*******************************************************************\

Function: smt2_convt::convert_relation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_relation(const exprt &expr)
{
  assert(expr.operands().size()==2);

  const typet &op_type=expr.op0().type();

  smt2_prop.out << "(";

  if(op_type.id()==ID_unsignedbv)
  {
    if(expr.id()==ID_le)
      smt2_prop.out << "bvule";
    else if(expr.id()==ID_lt)
      smt2_prop.out << "bvult";
    else if(expr.id()==ID_ge)
      smt2_prop.out << "bvuge";
    else if(expr.id()==ID_gt)
      smt2_prop.out << "bvugt";

    smt2_prop.out << " ";
    convert_expr(expr.op0());
    smt2_prop.out << " ";
    convert_expr(expr.op1());
  }
  else if(op_type.id()==ID_signedbv ||
          op_type.id()==ID_fixedbv)
  {
    if(expr.id()==ID_le)
      smt2_prop.out << "bvsle";
    else if(expr.id()==ID_lt)
      smt2_prop.out << "bvslt";
    else if(expr.id()==ID_ge)
      smt2_prop.out << "bvsge";
    else if(expr.id()==ID_gt)
      smt2_prop.out << "bvsgt";

    smt2_prop.out << " ";
    convert_expr(expr.op0());
    smt2_prop.out << " ";
    convert_expr(expr.op1());
  }
  else if(op_type.id()==ID_floatbv)
  {
    if(use_FPA_theory)
    {
      if(expr.id()==ID_le)
        smt2_prop.out << "<=";
      else if(expr.id()==ID_lt)
        smt2_prop.out << "<";
      else if(expr.id()==ID_ge)
        smt2_prop.out << ">=";
      else if(expr.id()==ID_gt)
        smt2_prop.out << ">";

      smt2_prop.out << " ";
      convert_expr(expr.op0());
      smt2_prop.out << " ";
      convert_expr(expr.op1());
    }
    else
    {
      if(expr.id()==ID_le)
        smt2_prop.out << "bvsle";
      else if(expr.id()==ID_lt)
        smt2_prop.out << "bvslt";
      else if(expr.id()==ID_ge)
        smt2_prop.out << "bvsge";
      else if(expr.id()==ID_gt)
        smt2_prop.out << "bvsgt";

      smt2_prop.out << " ";
      convert_expr(expr.op0());
      smt2_prop.out << " ";
      convert_expr(expr.op1());
    }
  }
  else if(op_type.id()==ID_rational || 
          op_type.id()==ID_integer)
  {
    smt2_prop.out << expr.id();

    smt2_prop.out << " ";
    convert_expr(expr.op0());
    smt2_prop.out << " ";
    convert_expr(expr.op1());
  }
  else
    throw "unsupported type for "+expr.id_string()+
          ": "+op_type.id_string();

  smt2_prop.out << ")";
}

/*******************************************************************\

Function: smt2_convt::convert_plus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_plus(const exprt &expr)
{
  assert(expr.operands().size()>=2);

  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv ||
     expr.type().id()==ID_fixedbv)
  {
    smt2_prop.out << "(bvadd";

    forall_operands(it, expr)
    {
      smt2_prop.out << " ";
      convert_expr(*it);
    }

    smt2_prop.out << ")";
  }
  else if(expr.type().id()==ID_floatbv)
  {
    // really ought to be binary only
    
    if(use_FPA_theory)
    {
      smt2_prop.out << "(+ RNE ";

      forall_operands(it, expr)
      {
        smt2_prop.out << " ";
        convert_expr(*it);
      }

      smt2_prop.out << ")";
    }
    else
    {
      throw "TODO: + for floatbv";
    }
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

    smt2_prop.out << "(bvadd ";
    convert_expr(p);
    smt2_prop.out << " ";
    smt2_prop.out << "((_ zero_extend " << BV_ADDR_BITS << ") ";

    if(element_size>=2)
    {
      smt2_prop.out << "(bvmul ";
      convert_expr(i);
      smt2_prop.out << " (_ bv" << element_size
                    << " " << boolbv_width(expr.type()) << "))";
    }
    else
      convert_expr(i);

    smt2_prop.out << "))";
  }
  else if(expr.type().id()==ID_rational)
  {
    smt2_prop.out << "(+";

    forall_operands(it, expr)
    {
      smt2_prop.out << " ";
      convert_expr(*it);
    }

    smt2_prop.out << ")";
  }
  else
    throw "unsupported type for +: "+expr.type().id_string();
}

/*******************************************************************\

Function: smt2_convt::convert_minus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_minus(const exprt &expr)
{
  assert(expr.operands().size()==2);

  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv ||
     expr.type().id()==ID_fixedbv)
  {
    smt2_prop.out << "(bvsub ";
    convert_expr(expr.op0());
    smt2_prop.out << " ";
    convert_expr(expr.op1());
    smt2_prop.out << ")";
  }
  else if(expr.type().id()==ID_floatbv)
  {
    if(use_FPA_theory)
    {
      smt2_prop.out << "(- ";
      convert_expr(expr.op0());
      smt2_prop.out << " ";
      convert_expr(expr.op1());
      smt2_prop.out << ")";
    }
    else
    {
      throw "TODO: - for floatbv";
    }
  }
  else if(expr.type().id()==ID_pointer)
  {
    convert_expr(binary_exprt(
        expr.op0(),
        "+",
        unary_minus_exprt(expr.op1(), expr.op1().type()),
        expr.type()));
  }
  else
    throw "unsupported type for -: "+expr.type().id_string();
}

/*******************************************************************\

Function: smt2_convt::convert_div

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_div(const exprt &expr)
{
  assert(expr.operands().size()==2);

  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv)
  {
    if(expr.type().id()==ID_unsignedbv)
      smt2_prop.out << "(bvudiv ";
    else
      smt2_prop.out << "(bvsdiv ";

    convert_expr(expr.op0());
    smt2_prop.out << " ";
    convert_expr(expr.op1());
    smt2_prop.out << ")";
  }
  else if(expr.type().id()==ID_fixedbv)
  {
    fixedbvt fbt(expr);
    unsigned fraction_bits=fbt.spec.get_fraction_bits();

    smt2_prop.out << "((_ extract " << fbt.spec.width-1 << " 0) ";
    smt2_prop.out << "(bvsdiv ";

    smt2_prop.out << "(concat ";
    convert_expr(expr.op0());
    smt2_prop.out << " (_ bv0 " << fraction_bits << ")) ";

    smt2_prop.out << "((_ sign_extend " << fraction_bits << ") ";
    convert_expr(expr.op1());
    smt2_prop.out << ")";

    smt2_prop.out << "))";
  }
  else if(expr.type().id()==ID_floatbv)
  {
    if(use_FPA_theory)
    {
      smt2_prop.out << "(/ RNE ";
      convert_expr(expr.op0());
      smt2_prop.out << " ";
      convert_expr(expr.op1());
      smt2_prop.out << ")";
    }
    else
    {
      throw "TODO: / for floatbv";
    }
  }
  else
    throw "unsupported type for /: "+expr.type().id_string();
}

/*******************************************************************\

Function: smt2_convt::convert_mul

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_mul(const exprt &expr)
{
  assert(expr.operands().size()>=2);

  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv)
  {
    forall_operands(it, expr)
      if(it!=expr.operands().begin()) smt2_prop.out << "(bvmul ";

    exprt::operandst::const_iterator last;

    forall_operands(it, expr)
    {
      if(it!=expr.operands().begin())
      {
        convert_expr(*last);
        smt2_prop.out << " ";
        convert_expr(*it);
        smt2_prop.out << ")";
      }

      last=it;
    }
  }
  else if(expr.type().id()==ID_floatbv)
  {
    if(use_FPA_theory)
    {
      forall_operands(it, expr)
        if(it!=expr.operands().begin())
          smt2_prop.out << "(* RNE ";

      exprt::operandst::const_iterator last;

      forall_operands(it, expr)
      {
        if(it!=expr.operands().begin())
        {
          convert_expr(*last);
          smt2_prop.out << " ";
          convert_expr(*it);
          smt2_prop.out << ")";
        }

        last=it;
      }
    }
    else
    {
      throw "TODO: * for floatbv";
    }
  }
  else if(expr.type().id()==ID_fixedbv)
  {
    fixedbvt fbt(expr);
    unsigned fraction_bits=fbt.spec.get_fraction_bits();

    smt2_prop.out << "((_ extract "
                  << fbt.spec.width+fraction_bits-1 << " "
                  << fraction_bits << ") ";

    forall_operands(it, expr)
      if(it!=expr.operands().begin())
        smt2_prop.out << "(bvmul ";

    exprt::operandst::const_iterator last;
    forall_operands(it, expr)
    {
      smt2_prop.out << "((_ sign_extend " << fraction_bits << ") ";
      convert_expr(*it);
      smt2_prop.out << ") ";

      if(it!=expr.operands().begin())
        smt2_prop.out << ")";
    }

    smt2_prop.out << ")";
  }
  else if(expr.type().id()==ID_rational)
  {
    smt2_prop.out << "(*";

    forall_operands(it, expr)
    {
      smt2_prop.out << " ";
      convert_expr(*it);
    }

    smt2_prop.out << ")";
  }
  else
    throw "unsupported type for *: "+expr.type().id_string();
}

/*******************************************************************\

Function: smt2_convt::convert_with

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_with(const exprt &expr)
{
  assert(expr.operands().size()>=3);
  
  const typet &expr_type=ns.follow(expr.type());

  if(expr_type.id()==ID_array)
  {
    smt2_prop.out << "(store ";

    convert_expr(expr.op0());

    for(unsigned i=1; i<expr.operands().size(); i+=2)
    {
      assert((i+1)<expr.operands().size());
      const exprt &index=expr.operands()[i];
      const exprt &value=expr.operands()[i+1];

      smt2_prop.out << " ";
      convert_expr(index);
      smt2_prop.out << " ";

      convert_expr(value);
    }

    smt2_prop.out << ")";
  }
  else if(expr_type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(expr_type);

    if(expr.operands().size()==3)
    {
      const exprt &index=expr.op1();
      const exprt &value=expr.op2();

      const irep_idt &component_name=index.get(ID_component_name);

      if(!struct_type.has_component(component_name))
        throw "with failed to find component in struct";

      unsigned update_number=struct_type.component_number(component_name);
      unsigned total_number=struct_type.components().size();

      smt2_prop.out << "((_ update "
                    << total_number << " "
                    << update_number << ") ";

      convert_expr(expr.op0());

      smt2_prop.out << " ";

      convert_expr(value);

      smt2_prop.out << ")"; // update
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
      
      boolbv_widtht boolbv_width(ns);

      unsigned total_width=boolbv_width(union_type);

      if(total_width==0)
        throw "failed to get union width for with";

      unsigned member_width=boolbv_width(value.type());

      if(member_width==0)
        throw "failed to get union member width for with";

      if(total_width==member_width)
      {
        // TODO: need to deal with booleans
        convert_expr(value);
      }
      else
      {
        assert(total_width>member_width);
        smt2_prop.out << "(concat ";
        smt2_prop.out << "((_ extract "
                      << (total_width-1)
                      << " " << member_width << ") ";
        convert_expr(expr.op0());
        smt2_prop.out << ") ";
        // TODO: need to deal with booleans
        convert_expr(value);
        smt2_prop.out << ")";
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

Function: smt2_convt::convert_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_index(const index_exprt &expr)
{
  assert(expr.operands().size()==2);

  smt2_prop.out << "(select ";
  convert_expr(expr.array());
  smt2_prop.out << " ";
  array_index(expr.index());
  smt2_prop.out << ")";
}

/*******************************************************************\

Function: smt2_convt::convert_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_member(const member_exprt &expr)
{
  assert(expr.operands().size()==1);

  const member_exprt &member_expr=to_member_expr(expr);
  const exprt &struct_op=member_expr.struct_op();
  const typet &struct_op_type=ns.follow(struct_op.type());
  const irep_idt &name=member_expr.get_component_name();

  if(struct_op_type.id()==ID_struct)
  {
    const struct_typet &struct_type=
      to_struct_type(struct_op_type);

    if(!struct_type.has_component(name))
      throw "failed to find struct member";

    unsigned number=struct_type.component_number(name);

    smt2_prop.out << "((_ project "
                  << struct_type.components().size()
                  << " " << (number+1) << ") ";
    convert_expr(struct_op);
    smt2_prop.out << ")";
  }
  else if(struct_op_type.id()==ID_union)
  {
    if(expr.type().id()==ID_signedbv ||
       expr.type().id()==ID_unsignedbv ||
       expr.type().id()==ID_fixedbv ||
       expr.type().id()==ID_bv)
    {
      boolbv_widtht boolbv_width(ns);
    
      unsigned width=boolbv_width(expr.type());
      
      if(width==0)
        throw "failed to get union member width";

      smt2_prop.out << "((_ extract "
                    << (width-1)
                    << " 0) ";
      convert_expr(struct_op);
      smt2_prop.out << ")";
    }
    else if(expr.type().id()==ID_bool)
    {
      smt2_prop.out << "(= ";
      smt2_prop.out << "((_ extract 0 0) ";
      convert_expr(struct_op);
      smt2_prop.out << ")";
      smt2_prop.out << " bit1)";
    }
    else
      throw "union member not implemented";
  }
  else
    assert(false);
}

/*******************************************************************\

Function: smt2_convt::convert_overflow

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_overflow(const exprt &expr)
{
}

/*******************************************************************\

Function: smt2_convt::set_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::set_to(const exprt &expr, bool value)
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

  smt2_prop.out << std::endl;

  assert(expr.type().id()==ID_bool);
  
  // special treatment for "set_to(a=b, true)" where
  // a is a new symbol

  if(expr.id()==ID_equal && value==true)
  {
    const equal_exprt &equal_expr=to_equal_expr(expr);

    if(equal_expr.lhs().id()==ID_symbol)
    {
      const irep_idt &identifier=to_symbol_expr(equal_expr.lhs()).get_identifier();
      
      if(identifier_map.find(identifier)==identifier_map.end())
      {
        identifiert &id=identifier_map[identifier];

        assert(id.type.is_nil());

        id.type=equal_expr.lhs().type();

        smt2_prop.out << "(define-fun ; set_to true" << std::endl
                      << " " << convert_identifier(identifier)
                      << " () ";

        convert_type(equal_expr.lhs().type());
        smt2_prop.out << " ";
        convert_expr(equal_expr.rhs());

        smt2_prop.out << ")" << std::endl;
        return; // done
      }
    }
  }

  find_symbols(expr);

  #if 0
  smt2_prop.out << "; CONV: "
                << from_expr(expr) << std::endl;
  #endif

  smt2_prop.out << "(assert ; set_to "
                << (value?"true":"false") << std::endl
                << " ";

  if(!value)
  {
    smt2_prop.out << "(not ";
    convert_expr(expr);
    smt2_prop.out << ")";
  }
  else
    convert_expr(expr);

  smt2_prop.out << ")" << std::endl;
}

/*******************************************************************\

Function: smt2_convt::find_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::find_symbols(const exprt &expr)
{
  find_symbols(expr.type());

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

    identifiert &id=identifier_map[identifier];

    if(id.type.is_nil())
    {
      id.type=expr.type();

      smt2_prop.out << "(declare-fun "
                    << convert_identifier(identifier)
                    << " () ";
      convert_type(expr.type());
      smt2_prop.out << ")" << std::endl;
    }
  }
  else if(expr.id()==ID_array_of)
  {
    if(array_of_map.find(expr)==array_of_map.end())
    {
      irep_idt id="array_of'"+i2string(array_of_map.size());
      smt2_prop.out << "; the following is a poor substitute for lambda i. x" << std::endl;
      smt2_prop.out << "(declare-fun "
                    << id
                    << " () ";
      convert_type(expr.type());
      smt2_prop.out << ")" << std::endl;

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
            smt2_prop.out
              << "(assert (= (select " << id
              << " (_ bv"
              << i << " " << array_index_bits << ")) ";
            convert_expr(expr.op0());
            smt2_prop.out << "))" << std::endl;
          }
        }
      }

      array_of_map[expr]=id;
    }
  }
  else if(expr.id()==ID_constant)
  {
    if(expr.type().id()==ID_array &&
       array_init_map.find(expr)==array_init_map.end())
    {
      // introduce a temporary array.
      irep_idt id="array_init'"+i2string(array_init_map.size());
      smt2_prop.out << "(declare-fun "
                    << id
                    << " () ";
      convert_type(expr.type());
      smt2_prop.out << ")" << std::endl;
      array_init_map[expr]=id;
    }
  }
  else if(expr.id()==ID_string_constant)
  {
    if(string2array_map.find(expr)==string2array_map.end())
    {
      exprt t=to_string_constant(expr).to_array_expr();
      string2array_map[expr]=t;

      // introduce a temporary array.
      irep_idt id="string'"+i2string(array_init_map.size());
      smt2_prop.out << "(declare-fun "
                    << id
                    << " () ";
      convert_type(t.type());
      smt2_prop.out << ")" << std::endl;
      array_init_map[t]=id;
    }
  }

}

/*******************************************************************\

Function: smt2_convt::convert_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_type(const typet &type)
{
  if(type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(type);

    smt2_prop.out << "(Array ";
    convert_type(array_index_type());
    smt2_prop.out << " ";
    convert_type(array_type.subtype());
    smt2_prop.out << ")";
  }
  else if(type.id()==ID_bool)
  {
    smt2_prop.out << "Bool";
  }
  else if(type.id()==ID_struct)
  {
    const struct_typet::componentst &components=
      to_struct_type(type).components();

    smt2_prop.out << "((_ Tuple " << components.size()
                  << ") ";

    for(unsigned i=0; i<components.size(); i++)
      convert_type(components[i].type());

    smt2_prop.out << ")";
  }
  else if(type.id()==ID_code)
  {
    // These may appear in structs.
    // We replace this by "Bool" in order to keep the same
    // member count.
    smt2_prop.out << "Bool";
  }
  else if(type.id()==ID_union)
  {
    boolbv_widtht boolbv_width(ns);
  
    unsigned width=boolbv_width(type);
    
    if(width==0)
      throw "failed to get width of union";

    smt2_prop.out << "(_ BitVec " << width << ")";
  }
  else if(type.id()==ID_pointer ||
          type.id()==ID_reference)
  {
    smt2_prop.out << "(_ BitVec "
                  << boolbv_width(type) << ")";
  }
  else if(type.id()==ID_bv ||
          type.id()==ID_fixedbv ||
          type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv ||
          type.id()==ID_c_enum)
  {
    smt2_prop.out << "(_ BitVec "
                  << to_bitvector_type(type).get_width() << ")";
  }
  else if(type.id()==ID_floatbv)
  {
    const floatbv_typet &floatbv_type=to_floatbv_type(type);
  
    if(use_FPA_theory)
      smt2_prop.out << "(_ FP "
                    << floatbv_type.get_e() << " "
                    << floatbv_type.get_f() << ")";
    else
      smt2_prop.out << "(_ BitVec "
                    << floatbv_type.get_width() << ")";
  }
  else if(type.id()==ID_rational)
    smt2_prop.out << "Real";
  else if(type.id()==ID_integer)
    smt2_prop.out << "Int";
  else if(type.id()==ID_symbol)
    convert_type(ns.follow(type));
  else
    throw "unsupported type: "+type.id_string();
}

/*******************************************************************\

Function: smt2_convt::find_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::find_symbols(const typet &type)
{
  std::set<irep_idt> recstack;
  find_symbols_rec(type, recstack);
}

/*******************************************************************\

Function: smt2_convt::find_symbols_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::find_symbols_rec(
  const typet &type, 
  std::set<irep_idt> &recstack)
{
  if(type.id()==ID_array)
   {
     const array_typet &array_type=to_array_type(type);
     find_symbols(array_type.size());
     find_symbols_rec(array_type.subtype(), recstack);
   }
   else if(type.id()==ID_incomplete_array)
   {
     find_symbols_rec(type.subtype(), recstack);
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
