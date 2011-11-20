/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <cstdlib>
#include <map>
#include <set>
#include <iostream>

#include <symbol.h>
#include <mp_arith.h>
#include <i2string.h>
#include <arith_tools.h>
#include <replace_expr.h>
#include <std_types.h>
#include <prefix.h>
#include <std_expr.h>
#include <threeval.h>

#include <ansi-c/string_constant.h>

#include "boolbv.h"
#include "boolbv_type.h"
#include "flatten_byte_operators.h"

#ifdef HAVE_FLOATBV
#include "../floatbv/float_utils.h"
#endif

#include "flatten_byte_operators.h"

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
    return prop_convt::literal(expr, dest);
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

      unsigned offset=integer2long(index*element_width);

      return literal(index_expr.array(), bit+offset, dest);
    }
    else if(expr.id()==ID_member)
    {
      const member_exprt &member_expr=to_member_expr(expr);

      const irept &components=expr.type().find(ID_components);
      const irep_idt &component_name=member_expr.get_component_name();

      unsigned offset=0;

      forall_irep(it, components.get_sub())
      {
        const typet &subtype=
          static_cast<const typet &>(it->find(ID_type));

        if(it->get(ID_name)==component_name)
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

void boolbvt::convert_bv(const exprt &expr, bvt &bv)
{
  // check cache first
  
  {
    bv_cachet::const_iterator cache_result=bv_cache.find(expr);
    if(cache_result!=bv_cache.end())
    {
      //std::cerr << "Cache hit on " << expr << "\n";
      bv=cache_result->second;
      return;
    }
  }
  
  convert_bitvector(expr, bv);
  
  // check
  for(unsigned i=0; i<bv.size(); i++)
    if(bv[i].var_no()==literalt::unused_var_no())
    {
      std::cout << "unused_var_no: " << expr.pretty() << std::endl;
      assert(false);
    }

  // insert into cache
  bv_cache.insert(std::pair<const exprt, bvt>(expr, bv));
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
    return convert_if(expr, bv);
  else if(expr.id()==ID_constant)
    return convert_constant(expr, bv);
  else if(expr.id()==ID_typecast)
    return convert_typecast(expr, bv);
  else if(expr.id()==ID_symbol)
    return convert_symbol(expr, bv);
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
    return convert_byte_extract(expr, bv);
  else if(expr.id()==ID_byte_update_little_endian ||
          expr.id()==ID_byte_update_big_endian)
    return convert_byte_update(expr, bv);
  else if(expr.id()==ID_nondet_symbol ||
          expr.id()=="quant_symbol")
    return convert_symbol(expr, bv);
  else if(expr.id()==ID_struct)
    return convert_struct(expr, bv);
  else if(expr.id()==ID_union)
    return convert_union(expr, bv);
  else if(expr.id()==ID_string_constant)
    return convert_bitvector(
      to_string_constant(expr).to_array_expr(), bv);
  else if(expr.id()==ID_array)
    return convert_array(expr, bv);
  else if(expr.id()==ID_lambda)
    return convert_lambda(expr, bv);
  else if(expr.id()==ID_array_of)
    return convert_array_of(expr, bv);
  else if(expr.id()==ID_function_application)
  {
    // make it free bits
    bv=prop.new_variables(boolbv_width(expr.type()));

    // record
    functions.record(to_function_application_expr(expr));
    
    return;
  }
  #ifdef HAVE_FLOATBV
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
  #endif

  return conversion_failed(expr, bv);
}

/*******************************************************************\

Function: boolbvt::convert_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_array(const exprt &expr, bvt &bv)
{
  unsigned width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr, bv);
    
  bv.resize(width);

  if(expr.type().id()==ID_array)
  {
    unsigned op_width=width/expr.operands().size();
    unsigned offset=0;
    
    forall_operands(it, expr)
    {
      bvt tmp;

      convert_bv(*it, tmp);

      if(tmp.size()!=op_width)
        throw "convert_array: unexpected operand width";

      for(unsigned j=0; j<op_width; j++)
        bv[offset+j]=tmp[j];

      offset+=op_width;
    }   

    return;
  }
  
  conversion_failed(expr, bv);
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

    exprt expr(expr.op1());
    replace_expr(expr.op0(), counter, expr);

    bvt tmp;
    convert_bv(expr, tmp);

    unsigned offset=integer2long(i*tmp.size());

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
    bv[i].set(atol(bv_sub[i].id().c_str()));
}

/*******************************************************************\

Function: boolbvt::convert_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_symbol(const exprt &expr, bvt &bv)
{
  unsigned width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr, bv);

  bv.resize(width);
  
  const irep_idt &identifier=expr.get(ID_identifier);

  if(identifier.empty())
    throw "convert_symbol got empty identifier";

  for(unsigned i=0; i<width; i++)
    bv[i]=map.get_literal(identifier, i, expr.type());

  for(unsigned i=0; i<width; i++)
    if(bv[i].var_no()>=prop.no_variables() &&
      !bv[i].is_constant()) { std::cout << identifier << std::endl; abort(); }
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
  
  // we perform some re-writing on the byte operators
  #if 0
  if(has_byte_operator(expr))
    return convert_rest(flatten_byte_operators(expr, ns));
  #endif

  // flatten any byte_* operators
  #if 0
  if(has_byte_operator(expr))
    return convert_rest(flatten_byte_operators(expr, ns));
  #endif

  const exprt::operandst &operands=expr.operands();

  if(expr.id()==ID_typecast)
    return convert_typecast(expr);
  else if(expr.id()==ID_equal)
    return convert_equality(to_equal_expr(expr));
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

    bvt bv;
    convert_bv(operands[0], bv);

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

    bvt bv;
    convert_bv(operands[0], bv);
    
    if(expr.op0().type().id()==ID_floatbv)
    {
      #ifdef HAVE_FLOATBV
      float_utilst float_utils(prop);
      float_utils.spec=to_floatbv_type(expr.op0().type());
      return float_utils.is_NaN(bv);
      #endif
    }
    else if(expr.op0().type().id()==ID_fixedbv)
      return const_literal(false);
  }
  else if(expr.id()==ID_isfinite)
  {
    if(expr.operands().size()!=1)
      throw "isfinite expects one operand";

    bvt bv;
    convert_bv(operands[0], bv);
    
    if(expr.op0().type().id()==ID_floatbv)
    {
      #ifdef HAVE_FLOATBV
      float_utilst float_utils(prop);
      float_utils.spec=to_floatbv_type(expr.op0().type());
      return prop.land(
        prop.lnot(float_utils.is_infinity(bv)),
        prop.lnot(float_utils.is_NaN(bv)));
      #endif
    }
    else if(expr.op0().type().id()==ID_fixedbv)
      return const_literal(true);
  }
  else if(expr.id()==ID_isinf)
  {
    if(expr.operands().size()!=1)
      throw "isinf expects one operand";

    bvt bv;
    convert_bv(operands[0], bv);
    
    if(expr.op0().type().id()==ID_floatbv)
    {
      #ifdef HAVE_FLOATBV
      float_utilst float_utils(prop);
      float_utils.spec=to_floatbv_type(expr.op0().type());
      return float_utils.is_infinity(bv);
      #endif
    }
    else if(expr.op0().type().id()==ID_fixedbv)
      return const_literal(false);
  }
  else if(expr.id()==ID_isnormal)
  {
    if(expr.operands().size()!=1)
      throw "isnormal expects one operand";

    bvt bv;
    convert_bv(operands[0], bv);
    
    if(expr.op0().type().id()==ID_floatbv)
    {
      #ifdef HAVE_FLOATBV
      float_utilst float_utils(prop);
      float_utils.spec=to_floatbv_type(expr.op0().type());
      return float_utils.is_normal(bv);
      #endif
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

bool boolbvt::boolbv_set_equality_to_true(const exprt &expr)
{
  if(!equality_propagation) return true;

  const exprt::operandst &operands=expr.operands();

  if(operands.size()==2)
  {
    const typet &type=ns.follow(operands[0].type());

    if(operands[0].id()==ID_symbol &&
       type==ns.follow(operands[1].type()) &&
       type.id()!=ID_bool)
    {
      // see if it is an unbounded array
      if(is_unbounded_array(type))
        return true;

      bvt bv1;
      convert_bv(operands[1], bv1);
      
      const irep_idt &identifier=
        operands[0].get(ID_identifier);

      for(unsigned i=0; i<bv1.size(); i++)
        map.set_literal(identifier, i, type, bv1[i]);

      return false;
    }
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
      if(!boolbv_set_equality_to_true(expr))
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
  dest=exprt("bv_literals", type);
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
  for(unsigned i=0; i<bv.size(); i++)
    bv[i]=prop.new_variable();

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
    out << it->first << "=";
    const boolbv_mapt::map_entryt &map_entry=it->second;

    std::string result="";
    for(unsigned i=0; i<map_entry.literal_map.size(); i++)
    {
      char ch='*';

      if(map_entry.literal_map[i].is_set)
      {
        tvt value=prop.l_get(map_entry.literal_map[i].l);
        if(value.is_true())
          ch='1';
        else if(value.is_false())
          ch='0';
        else
          ch='?';
      }
      
      result=result+ch;
    }
    
    out << result << std::endl;
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
