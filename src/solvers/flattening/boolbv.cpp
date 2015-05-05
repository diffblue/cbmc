/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <map>
#include <set>
#include <iostream>
#include <cstdlib> // abort()

#include <util/symbol.h>
#include <util/mp_arith.h>
#include <util/i2string.h>
#include <util/arith_tools.h>
#include <util/replace_expr.h>
#include <util/std_types.h>
#include <util/prefix.h>
#include <util/std_expr.h>
#include <util/threeval.h>
#include <util/string2int.h>

#include <ansi-c/string_constant.h>

#include "boolbv.h"
#include "boolbv_type.h"

#include "../floatbv/float_utils.h"

//#define DEBUG

/*******************************************************************\

Function: boolbvt::literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool boolbvt::literal(
  const exprt &expr,
  const unsigned bit,
  literalt &dest) const
{
  if(expr.type().id()==ID_bool)
  {
    assert(bit==0);
    return prop_conv_solvert::literal(expr, dest);
  }
  else
  {
    if(expr.id()==ID_symbol ||
       expr.id()==ID_nondet_symbol)
    {
      const irep_idt &identifier=expr.get(ID_identifier);

      boolbv_mapt::mappingt::const_iterator it_m=
        map.mapping.find(identifier);

      if(it_m==map.mapping.end()) return true;

      const boolbv_mapt::map_entryt &map_entry=it_m->second;
      
      assert(bit<map_entry.literal_map.size());
      if(!map_entry.literal_map[bit].is_set) return true;

      dest=map_entry.literal_map[bit].l;
      return false;
    }
    else if(expr.id()==ID_index)
    {
      const index_exprt &index_expr=to_index_expr(expr);

      unsigned element_width=boolbv_width(index_expr.type());
      
      if(element_width==0)
        throw "literal expects a bit-vector type";

      mp_integer index;
      if(to_integer(index_expr.index(), index))
        throw "literal expects constant index";

      unsigned offset=integer2unsigned(index*element_width);

      return literal(index_expr.array(), bit+offset, dest);
    }
    else if(expr.id()==ID_member)
    {
      const member_exprt &member_expr=to_member_expr(expr);

      const struct_typet::componentst &components=
        to_struct_type(expr.type()).components();
      const irep_idt &component_name=member_expr.get_component_name();

      unsigned offset=0;

      for(struct_typet::componentst::const_iterator
          it=components.begin();
          it!=components.end();
          it++)
      {
        const typet &subtype=it->type();

        if(it->get_name()==component_name)
          return literal(expr.op0(), bit+offset, dest);

        unsigned element_width=boolbv_width(subtype);

        if(element_width==0)
          throw "literal expects a bit-vector type";

        offset+=element_width;
      }

      throw "failed to find component";
    }
  }

  throw "found no literal for expression";
}

/*******************************************************************\

Function: boolbvt::convert_bv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const bvt& boolbvt::convert_bv(const exprt &expr)
{
  // check cache first
  std::pair<bv_cachet::iterator, bool> cache_result=
    bv_cache.insert(std::make_pair(expr, bvt()));
  if(!cache_result.second)
  {
    //std::cerr << "Cache hit on " << expr << "\n";
    return cache_result.first->second;
  }
  
  // Iterators into hash_maps supposedly stay stable
  // even though we are inserting more elements recursively.

  convert_bitvector(expr, cache_result.first->second);
  
  // check
  forall_literals(it, cache_result.first->second)
    if(it->var_no()==literalt::unused_var_no())
    {
      std::cout << "unused_var_no: " << expr.pretty() << std::endl;
      assert(false);
    }

  return cache_result.first->second;
}

/*******************************************************************\

Function: boolbvt::conversion_failed

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::conversion_failed(const exprt &expr, bvt &bv)
{
  ignoring(expr);

  // try to make it free bits
  unsigned width=boolbv_width(expr.type());

  bv.resize(width);

  for(unsigned i=0; i<width; i++)
    bv[i]=prop.new_variable();
}

/*******************************************************************\

Function: boolbvt::convert_bitvector

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_bitvector(const exprt &expr, bvt &bv)
{
  #ifdef DEBUG
  std::cout << "BV: " << expr.pretty() << std::endl;
  #endif

  if(expr.type().id()==ID_bool)
  {
    bv.resize(1);
    bv[0]=convert(expr);
    return;
  }

  if(expr.id()==ID_index)
    return convert_index(to_index_expr(expr), bv);
  else if(expr.id()==ID_constraint_select_one)
    return convert_constraint_select_one(expr, bv);
  else if(expr.id()==ID_member)
    return convert_member(to_member_expr(expr), bv);
  else if(expr.id()==ID_with)
    return convert_with(expr, bv);
  else if(expr.id()==ID_update)
    return convert_update(expr, bv);
  else if(expr.id()==ID_width)
  {
    unsigned result_width=boolbv_width(expr.type());

    if(result_width==0)
      return conversion_failed(expr, bv);

    if(expr.operands().size()!=1)
      return conversion_failed(expr, bv);

    unsigned op_width=boolbv_width(expr.op0().type());

    if(op_width==0)
      return conversion_failed(expr, bv);

    bv.resize(result_width);

    if(expr.type().id()==ID_unsignedbv ||
       expr.type().id()==ID_signedbv)
    {
      std::string binary=integer2binary(op_width/8, result_width);

      for(unsigned i=0; i<result_width; i++)
      {
        bool bit=(binary[binary.size()-i-1]=='1');
        bv[i]=const_literal(bit);
      }

      return;
    }
  }
  else if(expr.id()==ID_case)
    return convert_case(expr, bv);
  else if(expr.id()==ID_cond)
    return convert_cond(expr, bv);
  else if(expr.id()==ID_if)
    return convert_if(to_if_expr(expr), bv);
  else if(expr.id()==ID_constant)
    return convert_constant(to_constant_expr(expr), bv);
  else if(expr.id()==ID_typecast)
    return convert_typecast(to_typecast_expr(expr), bv);
  else if(expr.id()==ID_symbol)
    return convert_symbol(to_symbol_expr(expr), bv);
  else if(expr.id()==ID_bv_literals)
    return convert_bv_literals(expr, bv);
  else if(expr.id()==ID_plus || expr.id()==ID_minus ||
          expr.id()=="no-overflow-plus" ||
          expr.id()=="no-overflow-minus")
    return convert_add_sub(expr, bv);
  else if(expr.id()==ID_mult ||
          expr.id()=="no-overflow-mult")
    return convert_mult(expr, bv);
  else if(expr.id()==ID_div)
    return convert_div(expr, bv);
  else if(expr.id()==ID_mod)
    return convert_mod(expr, bv);
  else if(expr.id()==ID_shl || expr.id()==ID_ashr || expr.id()==ID_lshr)
    return convert_shift(expr, bv);
  else if(expr.id()==ID_floatbv_plus || expr.id()==ID_floatbv_minus ||
          expr.id()==ID_floatbv_mult || expr.id()==ID_floatbv_div)
    return convert_floatbv_op(expr, bv);
  else if(expr.id()==ID_floatbv_typecast)
    return convert_floatbv_typecast(to_floatbv_typecast_expr(expr), bv);
  else if(expr.id()==ID_concatenation)
    return convert_concatenation(expr, bv);
  else if(expr.id()==ID_replication)
    return convert_replication(expr, bv);
  else if(expr.id()==ID_extractbits)
    return convert_extractbits(to_extractbits_expr(expr), bv);
  else if(expr.id()==ID_bitnot || expr.id()==ID_bitand ||
          expr.id()==ID_bitor || expr.id()==ID_bitxor)
    return convert_bitwise(expr, bv);
  else if(expr.id()==ID_unary_minus ||
          expr.id()=="no-overflow-unary-minus")
    return convert_unary_minus(expr, bv);
  else if(expr.id()==ID_unary_plus)
  {
    assert(expr.operands().size()==1);
    return convert_bitvector(expr.op0(), bv);
  }
  else if(expr.id()==ID_abs)
    return convert_abs(expr, bv);
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
    return convert_byte_extract(to_byte_extract_expr(expr), bv);
  else if(expr.id()==ID_byte_update_little_endian ||
          expr.id()==ID_byte_update_big_endian)
    return convert_byte_update(to_byte_update_expr(expr), bv);
  else if(expr.id()==ID_nondet_symbol ||
          expr.id()=="quant_symbol")
    return convert_symbol(expr, bv);
  else if(expr.id()==ID_struct)
    return convert_struct(to_struct_expr(expr), bv);
  else if(expr.id()==ID_union)
    return convert_union(to_union_expr(expr), bv);
  else if(expr.id()==ID_string_constant)
    return convert_bitvector(
      to_string_constant(expr).to_array_expr(), bv);
  else if(expr.id()==ID_array)
    return convert_array(expr, bv);
  else if(expr.id()==ID_vector)
    return convert_vector(expr, bv);
  else if(expr.id()==ID_complex)
    return convert_complex(expr, bv);
  else if(expr.id()==ID_complex_real)
    return convert_complex_real(expr, bv);
  else if(expr.id()==ID_complex_imag)
    return convert_complex_imag(expr, bv);
  else if(expr.id()==ID_lambda)
    return convert_lambda(expr, bv);
  else if(expr.id()==ID_array_of)
    return convert_array_of(to_array_of_expr(expr), bv);
  else if(expr.id()==ID_let)
  {
    //const let_exprt &let_expr=to_let_expr(expr);
    throw "let is todo";
  }
  else if(expr.id()==ID_function_application)
  {
    // make it free bits
    bv=prop.new_variables(boolbv_width(expr.type()));

    // record
    functions.record(to_function_application_expr(expr));
    
    return;
  }
  else if(expr.id()==ID_float_debug1 ||
          expr.id()==ID_float_debug2)
  {
    assert(expr.operands().size()==2);
    bvt bv0, bv1;
    convert_bitvector(expr.op0(), bv0);
    convert_bitvector(expr.op1(), bv1);
    float_utilst float_utils(prop);
    float_utils.spec=to_floatbv_type(expr.type());
    bv=expr.id()==ID_float_debug1?
      float_utils.debug1(bv0, bv1):
      float_utils.debug2(bv0, bv1);
    return;
  }

  return conversion_failed(expr, bv);
}

/*******************************************************************\

Function: boolbvt::convert_lambda

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_lambda(const exprt &expr, bvt &bv)
{
  unsigned width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr, bv);

  if(expr.operands().size()!=2)
    throw "lambda takes two operands";

  if(expr.type().id()!=ID_array)
    return conversion_failed(expr, bv);

  const exprt &array_size=
    to_array_type(expr.type()).size();

  mp_integer size;

  if(to_integer(array_size, size))
    return conversion_failed(expr, bv);

  typet counter_type=expr.op0().type();

  for(mp_integer i=0; i<size; ++i)
  {
    exprt counter=from_integer(i, counter_type);

    exprt expr_op1(expr.op1());
    replace_expr(expr.op0(), counter, expr_op1);

    const bvt &tmp=convert_bv(expr_op1);

    unsigned offset=integer2unsigned(i*tmp.size());

    if(size*tmp.size()!=width)
      throw "convert_lambda: unexpected operand width";

    for(unsigned j=0; j<tmp.size(); j++)
      bv[offset+j]=tmp[j];
  }
}

/*******************************************************************\

Function: boolbvt::convert_bv_literals

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_bv_literals(const exprt &expr, bvt &bv)
{
  unsigned width=boolbv_width(expr.type());
  
  if(width==0)
    return conversion_failed(expr, bv);

  bv.resize(width);

  const irept::subt &bv_sub=expr.find(ID_bv).get_sub();

  if(bv_sub.size()!=width)
    throw "bv_literals with wrong size";

  for(unsigned i=0; i<width; i++)
    bv[i].set(unsafe_string2int(id2string(bv_sub[i].id())));
}

/*******************************************************************\

Function: boolbvt::convert_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_symbol(const exprt &expr, bvt &bv)
{
  const typet &type=expr.type();
  unsigned width=boolbv_width(type);

  bv.resize(width);
  
  const irep_idt &identifier=expr.get(ID_identifier);

  if(identifier.empty())
    throw "convert_symbol got empty identifier";

  if(width==0)
  {
    // just put in map
    map.get_map_entry(identifier, type);
  }
  else
  {
    map.get_literals(identifier, type, width, bv);

    forall_literals(it, bv)
      if(it->var_no()>=prop.no_variables() &&
        !it->is_constant()) { std::cout << identifier << std::endl; abort(); }
  }
}
   
/*******************************************************************\

Function: boolbvt::convert_rest

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolbvt::convert_rest(const exprt &expr)
{
  if(expr.type().id()!=ID_bool)
  {
    std::cerr << expr << std::endl;
    throw "boolbvt::convert_rest got non-boolean operand";
  }
  
  const exprt::operandst &operands=expr.operands();

  if(expr.id()==ID_typecast)
    return convert_typecast(expr);
  else if(expr.id()==ID_equal)
    return convert_equality(to_equal_expr(expr));
  else if(expr.id()==ID_verilog_case_equality ||
          expr.id()==ID_verilog_case_inequality)
    return convert_verilog_case_equality(to_binary_relation_expr(expr));
  else if(expr.id()==ID_notequal)
  {
    if(expr.operands().size()!=2)
      throw "notequal expects two operands";
    
    return prop.lnot(
      convert_equality(
        equal_exprt(expr.op0(), expr.op1())));
  }
  else if(expr.id()==ID_ieee_float_equal ||
          expr.id()==ID_ieee_float_notequal)
    return convert_ieee_float_rel(expr);
  else if(expr.id()==ID_le || expr.id()==ID_ge ||
          expr.id()==ID_lt  || expr.id()==ID_gt)
    return convert_bv_rel(expr);
  else if(expr.id()==ID_extractbit)
    return convert_extractbit(to_extractbit_expr(expr));
  else if(expr.id()==ID_forall)
    return convert_quantifier(expr);
  else if(expr.id()==ID_exists)
    return convert_quantifier(expr);
  else if(expr.id()==ID_index)
  {
    bvt bv;
    convert_index(to_index_expr(expr), bv);
    
    if(bv.size()!=1)
      throw "convert_index returned non-bool bitvector";

    return bv[0];
  }
  else if(expr.id()==ID_member)
  {
    bvt bv;
    convert_member(to_member_expr(expr), bv);
    
    if(bv.size()!=1)
      throw "convert_member returned non-bool bitvector";

    return bv[0];
  }
  else if(expr.id()==ID_case)
  {
    bvt bv;
    convert_case(expr, bv);

    if(bv.size()!=1)
      throw "convert_case returned non-bool bitvector";

    return bv[0];
  }
  else if(expr.id()==ID_cond)
  {
    bvt bv;
    convert_cond(expr, bv);

    if(bv.size()!=1)
      throw "convert_cond returned non-bool bitvector";

    return bv[0];
  }
  else if(expr.id()==ID_sign)
  {
    if(expr.operands().size()!=1)
      throw "sign expects one operand";

    const bvt &bv=convert_bv(operands[0]);

    if(bv.size()<1)
      throw "sign operator takes one non-empty operand";

    if(operands[0].type().id()==ID_signedbv)
      return bv[bv.size()-1];
    else if(operands[0].type().id()==ID_unsignedbv)
      return const_literal(false);
    else if(operands[0].type().id()==ID_fixedbv)
      return bv[bv.size()-1];
    else if(operands[0].type().id()==ID_floatbv)
      return bv[bv.size()-1];
  }
  else if(expr.id()==ID_reduction_or  || expr.id()==ID_reduction_and  ||
          expr.id()==ID_reduction_nor || expr.id()==ID_reduction_nand ||
          expr.id()==ID_reduction_xor || expr.id()==ID_reduction_xnor)
    return convert_reduction(expr);
  else if(has_prefix(expr.id_string(), "overflow-"))
    return convert_overflow(expr);
  else if(expr.id()==ID_isnan)
  {
    if(expr.operands().size()!=1)
      throw "isnan expects one operand";

    const bvt &bv=convert_bv(operands[0]);
    
    if(expr.op0().type().id()==ID_floatbv)
    {
      float_utilst float_utils(prop);
      float_utils.spec=to_floatbv_type(expr.op0().type());
      return float_utils.is_NaN(bv);
    }
    else if(expr.op0().type().id()==ID_fixedbv)
      return const_literal(false);
  }
  else if(expr.id()==ID_isfinite)
  {
    if(expr.operands().size()!=1)
      throw "isfinite expects one operand";

    const bvt &bv=convert_bv(operands[0]);
    
    if(expr.op0().type().id()==ID_floatbv)
    {
      float_utilst float_utils(prop);
      float_utils.spec=to_floatbv_type(expr.op0().type());
      return prop.land(
        prop.lnot(float_utils.is_infinity(bv)),
        prop.lnot(float_utils.is_NaN(bv)));
    }
    else if(expr.op0().type().id()==ID_fixedbv)
      return const_literal(true);
  }
  else if(expr.id()==ID_isinf)
  {
    if(expr.operands().size()!=1)
      throw "isinf expects one operand";

    const bvt &bv=convert_bv(operands[0]);
    
    if(expr.op0().type().id()==ID_floatbv)
    {
      float_utilst float_utils(prop);
      float_utils.spec=to_floatbv_type(expr.op0().type());
      return float_utils.is_infinity(bv);
    }
    else if(expr.op0().type().id()==ID_fixedbv)
      return const_literal(false);
  }
  else if(expr.id()==ID_isnormal)
  {
    if(expr.operands().size()!=1)
      throw "isnormal expects one operand";

    const bvt &bv=convert_bv(operands[0]);
    
    if(expr.op0().type().id()==ID_floatbv)
    {
      float_utilst float_utils(prop);
      float_utils.spec=to_floatbv_type(expr.op0().type());
      return float_utils.is_normal(bv);
    }
    else if(expr.op0().type().id()==ID_fixedbv)
      return const_literal(true);
  }

  return SUB::convert_rest(expr);
}

/*******************************************************************\

Function: boolbvt::boolbv_set_equality_to_true

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool boolbvt::boolbv_set_equality_to_true(const equal_exprt &expr)
{
  if(!equality_propagation) return true;

  const typet &type=ns.follow(expr.lhs().type());

  if(expr.lhs().id()==ID_symbol &&
     type==ns.follow(expr.rhs().type()) &&
     type.id()!=ID_bool)
  {
    // see if it is an unbounded array
    if(is_unbounded_array(type))
      return true;

    const bvt &bv1=convert_bv(expr.rhs());
    
    const irep_idt &identifier=
      to_symbol_expr(expr.lhs()).get_identifier();

    map.set_literals(identifier, type, bv1);

    return false;
  }

  return true;
}

/*******************************************************************\

Function: boolbvt::set_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::set_to(const exprt &expr, bool value)
{
  if(expr.type().id()!=ID_bool)
  {
    std::cerr << expr << std::endl;
    throw "boolbvt::set_to got non-boolean operand";
  }

  if(value)
  {
    if(expr.id()==ID_equal)
    {
      if(!boolbv_set_equality_to_true(to_equal_expr(expr)))
        return;
    }
  }

  return SUB::set_to(expr, value);
}

/*******************************************************************\

Function: boolbvt::make_bv_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::make_bv_expr(const typet &type, const bvt &bv, exprt &dest)
{
  dest=exprt(ID_bv_literals, type);
  irept::subt &bv_sub=dest.add(ID_bv).get_sub();

  bv_sub.resize(bv.size());

  for(unsigned i=0; i<bv.size(); i++)
    bv_sub[i].id(i2string(bv[i].get()));
}

/*******************************************************************\

Function: boolbvt::make_bv_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::make_free_bv_expr(const typet &type, exprt &dest)
{
  unsigned width=boolbv_width(type);

  if(width==0)
    throw "failed to get width of "+type.to_string();

  bvt bv;
  bv.resize(width);

  // make result free variables
  Forall_literals(it, bv)
    *it=prop.new_variable();

  make_bv_expr(type, bv, dest);
}

/*******************************************************************\

Function: boolbvt::is_unbounded_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool boolbvt::is_unbounded_array(const typet &type) const
{
  if(type.id()==ID_symbol) return is_unbounded_array(ns.follow(type));

  if(type.id()!=ID_array) return false;
  
  if(unbounded_array==U_ALL) return true;
  
  const exprt &size=to_array_type(type).size();
  
  mp_integer s;
  if(to_integer(size, s)) return true;

  if(unbounded_array==U_AUTO)
    if(s>1000) // magic number!
      return true;

  return false;
}

/*******************************************************************\

Function: boolbvt::print_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::print_assignment(std::ostream &out) const
{
  for(boolbv_mapt::mappingt::const_iterator it=map.mapping.begin();
      it!=map.mapping.end();
      it++)
  {
    out << it->first << "="
        << it->second.get_value(prop) << '\n';
  }
}

/*******************************************************************\

Function: boolbvt::build_offset_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::build_offset_map(const struct_typet &src, offset_mapt &dest)
{
  const struct_typet::componentst &components=
    src.components();

  dest.resize(components.size());
  unsigned offset=0;
  for(unsigned i=0; i<components.size(); i++)
  {
    unsigned comp_width=boolbv_width(components[i].type());
    dest[i]=offset;
    offset+=comp_width;
  }
}
