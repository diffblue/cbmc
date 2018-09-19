/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <cassert>
#include <map>
#include <set>

#include <util/arith_tools.h>
#include <util/magic.h>
#include <util/mp_arith.h>
#include <util/prefix.h>
#include <util/replace_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/string2int.h>
#include <util/string_constant.h>
#include <util/symbol.h>
#include <util/threeval.h>

#include "boolbv_type.h"

#include <solvers/floatbv/float_utils.h>
#include <solvers/lowering/expr_lowering.h>

bool boolbvt::literal(
  const exprt &expr,
  const std::size_t bit,
  literalt &dest) const
{
  if(expr.type().id()==ID_bool)
  {
    assert(bit==0);
    return prop_conv_solvert::literal(to_symbol_expr(expr), dest);
  }
  else
  {
    if(expr.id()==ID_symbol ||
       expr.id()==ID_nondet_symbol)
    {
      const irep_idt &identifier=expr.get(ID_identifier);

      boolbv_mapt::mappingt::const_iterator it_m=
        map.mapping.find(identifier);

      if(it_m==map.mapping.end())
        return true;

      const boolbv_mapt::map_entryt &map_entry=it_m->second;

      assert(bit<map_entry.literal_map.size());
      if(!map_entry.literal_map[bit].is_set)
        return true;

      dest=map_entry.literal_map[bit].l;
      return false;
    }
    else if(expr.id()==ID_index)
    {
      const index_exprt &index_expr=to_index_expr(expr);

      std::size_t element_width=boolbv_width(index_expr.type());

      if(element_width==0)
        throw "literal expects a bit-vector type";

      mp_integer index;
      if(to_integer(index_expr.index(), index))
        throw "literal expects constant index";

      std::size_t offset=integer2unsigned(index*element_width);

      return literal(index_expr.array(), bit+offset, dest);
    }
    else if(expr.id()==ID_member)
    {
      const member_exprt &member_expr=to_member_expr(expr);

      const struct_typet::componentst &components=
        to_struct_type(expr.type()).components();
      const irep_idt &component_name=member_expr.get_component_name();

      std::size_t offset=0;

      for(const auto &c : components)
      {
        const typet &subtype = c.type();

        if(c.get_name() == component_name)
          return literal(expr.op0(), bit+offset, dest);

        std::size_t element_width=boolbv_width(subtype);

        if(element_width==0)
          throw "literal expects a bit-vector type";

        offset+=element_width;
      }

      throw "failed to find component";
    }
  }

  throw "found no literal for expression";
}

const bvt &boolbvt::convert_bv(const exprt &expr)
{
  // check cache first
  std::pair<bv_cachet::iterator, bool> cache_result=
    bv_cache.insert(std::make_pair(expr, bvt()));
  if(!cache_result.second)
  {
    return cache_result.first->second;
  }

  // Iterators into hash_maps supposedly stay stable
  // even though we are inserting more elements recursively.

  cache_result.first->second=convert_bitvector(expr);

  // check
  forall_literals(it, cache_result.first->second)
  {
    if(freeze_all && !it->is_constant())
      prop.set_frozen(*it);
    if(it->var_no()==literalt::unused_var_no())
    {
      error() << "unused_var_no: " << expr.pretty() << eom;
      assert(false);
    }
  }

  return cache_result.first->second;
}

bvt boolbvt::conversion_failed(const exprt &expr)
{
  ignoring(expr);

  // try to make it free bits
  std::size_t width=boolbv_width(expr.type());
  return prop.new_variables(width);
}

/// Converts an expression into its gate-level representation and returns a
/// vector of literals corresponding to the outputs of the Boolean circuit.
/// \param expr: Expression to convert
/// \return A vector of literals corresponding to the outputs of the Boolean
///   circuit
/// \throws bitvector_conversion_exceptiont raised if converting byte_extraction
/// goes wrong.
/// TODO: extend for other types of conversion exception (diffblue/cbmc#2103).
bvt boolbvt::convert_bitvector(const exprt &expr)
{
  if(expr.type().id()==ID_bool)
  {
    bvt bv;
    bv.resize(1);
    bv[0]=convert(expr);
    return bv;
  }

  if(expr.id()==ID_index)
    return convert_index(to_index_expr(expr));
  else if(expr.id()==ID_constraint_select_one)
    return convert_constraint_select_one(expr);
  else if(expr.id()==ID_member)
    return convert_member(to_member_expr(expr));
  else if(expr.id()==ID_with)
    return convert_with(expr);
  else if(expr.id()==ID_update)
    return convert_update(expr);
  else if(expr.id()==ID_width)
  {
    std::size_t result_width=boolbv_width(expr.type());

    if(result_width==0)
      return conversion_failed(expr);

    if(expr.operands().size()!=1)
      return conversion_failed(expr);

    std::size_t op_width=boolbv_width(expr.op0().type());

    if(op_width==0)
      return conversion_failed(expr);

    if(expr.type().id()==ID_unsignedbv ||
       expr.type().id()==ID_signedbv)
      return bv_utils.build_constant(op_width/8, result_width);
  }
  else if(expr.id()==ID_case)
    return convert_case(expr);
  else if(expr.id()==ID_cond)
    return convert_cond(expr);
  else if(expr.id()==ID_if)
    return convert_if(to_if_expr(expr));
  else if(expr.id()==ID_constant)
    return convert_constant(to_constant_expr(expr));
  else if(expr.id()==ID_typecast)
    return convert_bv_typecast(to_typecast_expr(expr));
  else if(expr.id()==ID_symbol)
    return convert_symbol(to_symbol_expr(expr));
  else if(expr.id()==ID_bv_literals)
    return convert_bv_literals(expr);
  else if(expr.id()==ID_plus || expr.id()==ID_minus ||
          expr.id()=="no-overflow-plus" ||
          expr.id()=="no-overflow-minus")
    return convert_add_sub(expr);
  else if(expr.id()==ID_mult ||
          expr.id()=="no-overflow-mult")
    return convert_mult(expr);
  else if(expr.id()==ID_div)
    return convert_div(to_div_expr(expr));
  else if(expr.id()==ID_mod)
    return convert_mod(to_mod_expr(expr));
  else if(expr.id()==ID_shl || expr.id()==ID_ashr || expr.id()==ID_lshr ||
          expr.id()==ID_rol || expr.id()==ID_ror)
    return convert_shift(to_shift_expr(expr));
  else if(expr.id()==ID_floatbv_plus || expr.id()==ID_floatbv_minus ||
          expr.id()==ID_floatbv_mult || expr.id()==ID_floatbv_div ||
          expr.id()==ID_floatbv_rem)
    return convert_floatbv_op(expr);
  else if(expr.id()==ID_floatbv_typecast)
    return convert_floatbv_typecast(to_floatbv_typecast_expr(expr));
  else if(expr.id()==ID_concatenation)
    return convert_concatenation(expr);
  else if(expr.id()==ID_replication)
    return convert_replication(to_replication_expr(expr));
  else if(expr.id()==ID_extractbits)
    return convert_extractbits(to_extractbits_expr(expr));
  else if(expr.id()==ID_bitnot || expr.id()==ID_bitand ||
          expr.id()==ID_bitor || expr.id()==ID_bitxor ||
          expr.id()==ID_bitxnor || expr.id()==ID_bitnor ||
          expr.id()==ID_bitnand)
    return convert_bitwise(expr);
  else if(expr.id()==ID_unary_minus ||
          expr.id()=="no-overflow-unary-minus")
    return convert_unary_minus(to_unary_expr(expr));
  else if(expr.id()==ID_unary_plus)
  {
    return convert_bitvector(to_unary_plus_expr(expr).op());
  }
  else if(expr.id()==ID_abs)
    return convert_abs(to_abs_expr(expr));
  else if(expr.id() == ID_bswap)
    return convert_bswap(to_bswap_expr(expr));
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
    return convert_byte_extract(to_byte_extract_expr(expr));
  else if(expr.id()==ID_byte_update_little_endian ||
          expr.id()==ID_byte_update_big_endian)
    return convert_byte_update(to_byte_update_expr(expr));
  else if(expr.id()==ID_nondet_symbol ||
          expr.id()=="quant_symbol")
    return convert_symbol(expr);
  else if(expr.id()==ID_struct)
    return convert_struct(to_struct_expr(expr));
  else if(expr.id()==ID_union)
    return convert_union(to_union_expr(expr));
  else if(expr.id()==ID_string_constant)
    return convert_bitvector(
      to_string_constant(expr).to_array_expr());
  else if(expr.id()==ID_array)
    return convert_array(expr);
  else if(expr.id()==ID_vector)
    return convert_vector(expr);
  else if(expr.id()==ID_complex)
    return convert_complex(expr);
  else if(expr.id()==ID_complex_real)
    return convert_complex_real(to_complex_real_expr(expr));
  else if(expr.id()==ID_complex_imag)
    return convert_complex_imag(to_complex_imag_expr(expr));
  else if(expr.id()==ID_lambda)
    return convert_lambda(expr);
  else if(expr.id()==ID_array_of)
    return convert_array_of(to_array_of_expr(expr));
  else if(expr.id()==ID_let)
    return convert_let(to_let_expr(expr));
  else if(expr.id()==ID_function_application)
    return convert_function_application(
      to_function_application_expr(expr));
  else if(expr.id()==ID_reduction_or  || expr.id()==ID_reduction_and  ||
          expr.id()==ID_reduction_nor || expr.id()==ID_reduction_nand ||
          expr.id()==ID_reduction_xor || expr.id()==ID_reduction_xnor)
    return convert_bv_reduction(to_unary_expr(expr));
  else if(expr.id()==ID_not)
    return convert_not(to_not_expr(expr));
  else if(expr.id()==ID_power)
     return convert_power(to_binary_expr(expr));
  else if(expr.id()==ID_float_debug1 ||
          expr.id()==ID_float_debug2)
  {
    assert(expr.operands().size()==2);
    bvt bv0=convert_bitvector(expr.op0());
    bvt bv1=convert_bitvector(expr.op1());
    float_utilst float_utils(prop, to_floatbv_type(expr.type()));
    bvt bv=expr.id()==ID_float_debug1?
      float_utils.debug1(bv0, bv1):
      float_utils.debug2(bv0, bv1);
    return bv;
  }
  else if(expr.id() == ID_popcount)
    return convert_bv(lower_popcount(to_popcount_expr(expr), ns));

  return conversion_failed(expr);
}

bvt boolbvt::convert_lambda(const exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  if(expr.operands().size()!=2)
    throw "lambda takes two operands";

  if(expr.type().id()!=ID_array)
    return conversion_failed(expr);

  const exprt &array_size=
    to_array_type(expr.type()).size();

  mp_integer size;

  if(to_integer(array_size, size))
    return conversion_failed(expr);

  typet counter_type=expr.op0().type();

  bvt bv;
  bv.resize(width);

  for(mp_integer i=0; i<size; ++i)
  {
    exprt counter=from_integer(i, counter_type);

    exprt expr_op1(expr.op1());
    replace_expr(expr.op0(), counter, expr_op1);

    const bvt &tmp=convert_bv(expr_op1);

    std::size_t offset=integer2unsigned(i*tmp.size());

    if(size*tmp.size()!=width)
      throw "convert_lambda: unexpected operand width";

    for(std::size_t j=0; j<tmp.size(); j++)
      bv[offset+j]=tmp[j];
  }

  return bv;
}

bvt boolbvt::convert_bv_literals(const exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  bvt bv;
  bv.resize(width);

  const irept::subt &bv_sub=expr.find(ID_bv).get_sub();

  if(bv_sub.size()!=width)
    throw "bv_literals with wrong size";

  for(std::size_t i=0; i<width; i++)
    bv[i].set(unsafe_string2unsigned(id2string(bv_sub[i].id())));

  return bv;
}

bvt boolbvt::convert_symbol(const exprt &expr)
{
  const typet &type=expr.type();
  std::size_t width=boolbv_width(type);

  bvt bv;
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
        !it->is_constant())
      {
        error() << identifier << eom;
        assert(false);
      }
  }

  return bv;
}


bvt boolbvt::convert_function_application(
  const function_application_exprt &expr)
{
  // record
  functions.record(expr);

  // make it free bits
  return prop.new_variables(boolbv_width(expr.type()));
}


literalt boolbvt::convert_rest(const exprt &expr)
{
  PRECONDITION(expr.type().id() == ID_bool);
  const exprt::operandst &operands=expr.operands();

  if(expr.id()==ID_typecast)
    return convert_typecast(to_typecast_expr(expr));
  else if(expr.id()==ID_equal)
    return convert_equality(to_equal_expr(expr));
  else if(expr.id()==ID_verilog_case_equality ||
          expr.id()==ID_verilog_case_inequality)
    return convert_verilog_case_equality(to_binary_relation_expr(expr));
  else if(expr.id()==ID_notequal)
  {
    DATA_INVARIANT(expr.operands().size() == 2, "notequal expects two operands");
    return !convert_equality(equal_exprt(expr.op0(), expr.op1()));
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
  else if(expr.id()==ID_let)
  {
    bvt bv=convert_let(to_let_expr(expr));

    DATA_INVARIANT(bv.size()==1,
      "convert_let must return 1-bit vector for boolean let");

    return bv[0];
  }
  else if(expr.id()==ID_index)
  {
    bvt bv=convert_index(to_index_expr(expr));
    CHECK_RETURN(bv.size() == 1);
    return bv[0];
  }
  else if(expr.id()==ID_member)
  {
    bvt bv=convert_member(to_member_expr(expr));
    CHECK_RETURN(bv.size() == 1);
    return bv[0];
  }
  else if(expr.id()==ID_case)
  {
    bvt bv=convert_case(expr);
    CHECK_RETURN(bv.size() == 1);
    return bv[0];
  }
  else if(expr.id()==ID_cond)
  {
    bvt bv=convert_cond(expr);
    CHECK_RETURN(bv.size() == 1);
    return bv[0];
  }
  else if(expr.id()==ID_sign)
  {
    DATA_INVARIANT(expr.operands().size() == 1, "sign expects one operand");
    const bvt &bv=convert_bv(operands[0]);
    CHECK_RETURN(!bv.empty());
    const irep_idt type_id = operands[0].type().id();
    if(type_id == ID_signedbv || type_id == ID_fixedbv || type_id == ID_floatbv)
      return bv[bv.size()-1];
    if(type_id == ID_unsignedbv)
      return const_literal(false);
  }
  else if(expr.id()==ID_reduction_or  || expr.id()==ID_reduction_and  ||
          expr.id()==ID_reduction_nor || expr.id()==ID_reduction_nand ||
          expr.id()==ID_reduction_xor || expr.id()==ID_reduction_xnor)
    return convert_reduction(to_unary_expr(expr));
  else if(expr.id()==ID_onehot || expr.id()==ID_onehot0)
    return convert_onehot(to_unary_expr(expr));
  else if(has_prefix(expr.id_string(), "overflow-"))
    return convert_overflow(expr);
  else if(expr.id()==ID_isnan)
  {
    DATA_INVARIANT(expr.operands().size() == 1, "isnan expects one operand");
    const bvt &bv=convert_bv(operands[0]);

    if(expr.op0().type().id()==ID_floatbv)
    {
      float_utilst float_utils(prop, to_floatbv_type(expr.op0().type()));
      return float_utils.is_NaN(bv);
    }
    else if(expr.op0().type().id() == ID_fixedbv)
      return const_literal(false);
  }
  else if(expr.id()==ID_isfinite)
  {
    DATA_INVARIANT(expr.operands().size() == 1, "isfinite expects one operand");
    const bvt &bv=convert_bv(operands[0]);
    if(expr.op0().type().id()==ID_floatbv)
    {
      float_utilst float_utils(prop, to_floatbv_type(expr.op0().type()));
      return prop.land(
        !float_utils.is_infinity(bv),
        !float_utils.is_NaN(bv));
    }
    else if(expr.op0().type().id() == ID_fixedbv)
      return const_literal(true);
  }
  else if(expr.id()==ID_isinf)
  {
    DATA_INVARIANT(expr.operands().size() == 1, "isinf expects one operand");
    const bvt &bv=convert_bv(operands[0]);
    if(expr.op0().type().id()==ID_floatbv)
    {
      float_utilst float_utils(prop, to_floatbv_type(expr.op0().type()));
      return float_utils.is_infinity(bv);
    }
    else if(expr.op0().type().id() == ID_fixedbv)
      return const_literal(false);
  }
  else if(expr.id()==ID_isnormal)
  {
    DATA_INVARIANT(expr.operands().size() == 1, "isnormal expects one operand");
    if(expr.op0().type().id()==ID_floatbv)
    {
      const bvt &bv = convert_bv(operands[0]);
      float_utilst float_utils(prop, to_floatbv_type(expr.op0().type()));
      return float_utils.is_normal(bv);
    }
    else if(expr.op0().type().id() == ID_fixedbv)
      return const_literal(true);
  }

  return SUB::convert_rest(expr);
}

bool boolbvt::boolbv_set_equality_to_true(const equal_exprt &expr)
{
  if(!equality_propagation)
    return true;

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

    if(freeze_all)
      set_frozen(bv1);

    return false;
  }

  return true;
}

void boolbvt::set_to(const exprt &expr, bool value)
{
  PRECONDITION(expr.type().id() == ID_bool);

  const auto equal_expr = expr_try_dynamic_cast<equal_exprt>(expr);
  if(value && equal_expr && !boolbv_set_equality_to_true(*equal_expr))
    return;
  SUB::set_to(expr, value);
}

exprt boolbvt::make_bv_expr(const typet &type, const bvt &bv)
{
  exprt dest(ID_bv_literals, type);
  irept::subt &bv_sub=dest.add(ID_bv).get_sub();
  bv_sub.resize(bv.size());

  for(std::size_t i=0; i<bv.size(); i++)
    bv_sub[i].id(std::to_string(bv[i].get()));
  return dest;
}

exprt boolbvt::make_free_bv_expr(const typet &type)
{
  const std::size_t width = boolbv_width(type);
  PRECONDITION(width != 0);
  bvt bv(width);
  for(auto &lit : bv)
    lit = prop.new_variable();
  return make_bv_expr(type, bv);
}

bool boolbvt::is_unbounded_array(const typet &type) const
{
  if(type.id()==ID_symbol)
    return is_unbounded_array(ns.follow(type));

  if(type.id()!=ID_array)
    return false;

  if(unbounded_array==unbounded_arrayt::U_ALL)
    return true;

  const exprt &size=to_array_type(type).size();

  mp_integer s;
  if(to_integer(size, s))
    return true;

  if(unbounded_array==unbounded_arrayt::U_AUTO)
    if(s>MAX_FLATTENED_ARRAY_SIZE)
      return true;

  return false;
}

void boolbvt::print_assignment(std::ostream &out) const
{
  arrayst::print_assignment(out);
  for(const auto &pair : map.mapping)
    out << pair.first << "=" << pair.second.get_value(prop) << '\n';
}

boolbvt::offset_mapt boolbvt::build_offset_map(const struct_typet &src)
{
  const struct_typet::componentst &components = src.components();
  offset_mapt dest;
  dest.reserve(components.size());
  std::size_t offset = 0;
  for(const auto &comp : components)
  {
    dest.push_back(offset);
    offset += boolbv_width(comp.type());
  }
  return dest;
}
