/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <algorithm>

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/byte_operators.h>
#include <util/config.h>
#include <util/floatbv_expr.h>
#include <util/magic.h>
#include <util/mp_arith.h>
#include <util/replace_expr.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/string2int.h>
#include <util/string_constant.h>

#include <solvers/floatbv/float_utils.h>

endianness_mapt boolbvt::endianness_map(const typet &type) const
{
  const bool little_endian =
    config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN;
  return endianness_map(type, little_endian);
}

/// Convert expression to vector of literalts, using an internal
/// cache to speed up conversion if available. Also assert the resultant
/// vector is of a specific size, and freeze any elements if appropriate.
const bvt &
boolbvt::convert_bv(const exprt &expr, optionalt<std::size_t> expected_width)
{
  // check cache first
  std::pair<bv_cachet::iterator, bool> cache_result=
    bv_cache.insert(std::make_pair(expr, bvt()));

  // get a reference to the cache entry
  auto &cache_entry = cache_result.first->second;

  if(!cache_result.second)
  {
    // Found in cache
    return cache_entry;
  }

  // Iterators into hash_maps do not remain valid when inserting
  // more elements recursively. C++11 §23.2.5/13
  // However, the _reference_ to the entry does!
  cache_entry = convert_bitvector(expr);

  INVARIANT_WITH_DIAGNOSTICS(
    !expected_width || cache_entry.size() == *expected_width,
    "bitvector width shall match the indicated expected width",
    expr.find_source_location(),
    irep_pretty_diagnosticst(expr));

  // check
  for(const auto &literal : cache_entry)
  {
    if(freeze_all && !literal.is_constant())
      prop.set_frozen(literal);

    INVARIANT_WITH_DIAGNOSTICS(
      literal.var_no() != literalt::unused_var_no(),
      "variable number must be different from the unused variable number",
      expr.find_source_location(),
      irep_pretty_diagnosticst(expr));
  }

  return cache_entry;
}

/// Print that the expression of x has failed conversion,
/// then return a vector of x's width.
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
bvt boolbvt::convert_bitvector(const exprt &expr)
{
  if(expr.type().id()==ID_bool)
    return {convert(expr)};

  if(expr.id()==ID_index)
    return convert_index(to_index_expr(expr));
  else if(expr.id()==ID_constraint_select_one)
    return convert_constraint_select_one(expr);
  else if(expr.id()==ID_member)
    return convert_member(to_member_expr(expr));
  else if(expr.id()==ID_with)
    return convert_with(to_with_expr(expr));
  else if(expr.id()==ID_update)
    return convert_update(to_update_expr(expr));
  else if(expr.id()==ID_case)
    return convert_case(expr);
  else if(expr.id()==ID_cond)
    return convert_cond(to_cond_expr(expr));
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
  else if(expr.id() == ID_mult)
    return convert_mult(to_mult_expr(expr));
  else if(expr.id()==ID_div)
    return convert_div(to_div_expr(expr));
  else if(expr.id()==ID_mod)
    return convert_mod(to_mod_expr(expr));
  else if(expr.id()==ID_shl || expr.id()==ID_ashr || expr.id()==ID_lshr ||
          expr.id()==ID_rol || expr.id()==ID_ror)
    return convert_shift(to_shift_expr(expr));
  else if(
    expr.id() == ID_floatbv_plus || expr.id() == ID_floatbv_minus ||
    expr.id() == ID_floatbv_mult || expr.id() == ID_floatbv_div)
  {
    return convert_floatbv_op(to_ieee_float_op_expr(expr));
  }
  else if(expr.id() == ID_floatbv_mod)
    return convert_floatbv_mod_rem(to_binary_expr(expr));
  else if(expr.id() == ID_floatbv_rem)
    return convert_floatbv_mod_rem(to_binary_expr(expr));
  else if(expr.id()==ID_floatbv_typecast)
    return convert_floatbv_typecast(to_floatbv_typecast_expr(expr));
  else if(expr.id()==ID_concatenation)
    return convert_concatenation(to_concatenation_expr(expr));
  else if(expr.id()==ID_replication)
    return convert_replication(to_replication_expr(expr));
  else if(expr.id()==ID_extractbits)
    return convert_extractbits(to_extractbits_expr(expr));
  else if(expr.id()==ID_bitnot || expr.id()==ID_bitand ||
          expr.id()==ID_bitor || expr.id()==ID_bitxor ||
          expr.id()==ID_bitxnor || expr.id()==ID_bitnor ||
          expr.id()==ID_bitnand)
    return convert_bitwise(expr);
  else if(expr.id() == ID_unary_minus)
    return convert_unary_minus(to_unary_minus_expr(expr));
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
  else if(expr.id() == ID_empty_union)
    return convert_empty_union(to_empty_union_expr(expr));
  else if(expr.id()==ID_string_constant)
    return convert_bitvector(
      to_string_constant(expr).to_array_expr());
  else if(expr.id()==ID_array)
    return convert_array(expr);
  else if(expr.id()==ID_vector)
    return convert_vector(to_vector_expr(expr));
  else if(expr.id()==ID_complex)
    return convert_complex(to_complex_expr(expr));
  else if(expr.id()==ID_complex_real)
    return convert_complex_real(to_complex_real_expr(expr));
  else if(expr.id()==ID_complex_imag)
    return convert_complex_imag(to_complex_imag_expr(expr));
  else if(expr.id() == ID_array_comprehension)
    return convert_array_comprehension(to_array_comprehension_expr(expr));
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
  else if(expr.id() == ID_popcount)
    return convert_bv(simplify_expr(to_popcount_expr(expr).lower(), ns));
  else if(expr.id() == ID_count_leading_zeros)
  {
    return convert_bv(
      simplify_expr(to_count_leading_zeros_expr(expr).lower(), ns));
  }
  else if(expr.id() == ID_count_trailing_zeros)
  {
    return convert_bv(
      simplify_expr(to_count_trailing_zeros_expr(expr).lower(), ns));
  }
  else if(expr.id() == ID_bitreverse)
    return convert_bitreverse(to_bitreverse_expr(expr));
  else if(expr.id() == ID_saturating_minus || expr.id() == ID_saturating_plus)
    return convert_saturating_add_sub(to_binary_expr(expr));

  return conversion_failed(expr);
}

bvt boolbvt::convert_array_comprehension(const array_comprehension_exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  const exprt &array_size = expr.type().size();

  const auto size = numeric_cast<mp_integer>(array_size);

  if(!size.has_value())
    return conversion_failed(expr);

  typet counter_type = expr.arg().type();

  bvt bv;
  bv.resize(width);

  for(mp_integer i = 0; i < *size; ++i)
  {
    exprt counter=from_integer(i, counter_type);

    exprt body = expr.body();
    replace_expr(expr.arg(), counter, body);

    const bvt &tmp = convert_bv(body);

    INVARIANT(
      *size * tmp.size() == width,
      "total bitvector width shall equal the number of operands times the size "
      "per operand");

    std::size_t offset = numeric_cast_v<std::size_t>(i * tmp.size());

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

  const irep_idt &identifier = expr.get(ID_identifier);
  CHECK_RETURN(!identifier.empty());

  bvt bv = map.get_literals(identifier, type, width);

  INVARIANT_WITH_DIAGNOSTICS(
    std::all_of(
      bv.begin(),
      bv.end(),
      [this](const literalt &l) {
        return l.var_no() < prop.no_variables() || l.is_constant();
      }),
    "variable number of non-constant literals should be within bounds",
    id2string(identifier));

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

  if(expr.id()==ID_typecast)
    return convert_typecast(to_typecast_expr(expr));
  else if(expr.id()==ID_equal)
    return convert_equality(to_equal_expr(expr));
  else if(expr.id()==ID_verilog_case_equality ||
          expr.id()==ID_verilog_case_inequality)
    return convert_verilog_case_equality(to_binary_relation_expr(expr));
  else if(expr.id()==ID_notequal)
  {
    const auto &notequal_expr = to_notequal_expr(expr);
    return !convert_equality(
      equal_exprt(notequal_expr.lhs(), notequal_expr.rhs()));
  }
  else if(expr.id()==ID_ieee_float_equal ||
          expr.id()==ID_ieee_float_notequal)
  {
    return convert_ieee_float_rel(to_binary_relation_expr(expr));
  }
  else if(expr.id()==ID_le || expr.id()==ID_ge ||
          expr.id()==ID_lt  || expr.id()==ID_gt)
  {
    return convert_bv_rel(to_binary_relation_expr(expr));
  }
  else if(expr.id()==ID_extractbit)
    return convert_extractbit(to_extractbit_expr(expr));
  else if(expr.id()==ID_forall)
    return convert_quantifier(to_quantifier_expr(expr));
  else if(expr.id()==ID_exists)
    return convert_quantifier(to_quantifier_expr(expr));
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
    bvt bv = convert_cond(to_cond_expr(expr));
    CHECK_RETURN(bv.size() == 1);
    return bv[0];
  }
  else if(expr.id()==ID_sign)
  {
    const auto &op = to_sign_expr(expr).op();
    const bvt &bv = convert_bv(op);
    CHECK_RETURN(!bv.empty());
    const irep_idt type_id = op.type().id();
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
  else if(
    can_cast_expr<binary_overflow_exprt>(expr) ||
    can_cast_expr<unary_minus_overflow_exprt>(expr))
  {
    return convert_overflow(expr);
  }
  else if(expr.id()==ID_isnan)
  {
    const auto &op = to_unary_expr(expr).op();
    const bvt &bv = convert_bv(op);

    if(op.type().id() == ID_floatbv)
    {
      float_utilst float_utils(prop, to_floatbv_type(op.type()));
      return float_utils.is_NaN(bv);
    }
    else if(op.type().id() == ID_fixedbv)
      return const_literal(false);
  }
  else if(expr.id()==ID_isfinite)
  {
    const auto &op = to_unary_expr(expr).op();
    const bvt &bv = convert_bv(op);

    if(op.type().id() == ID_floatbv)
    {
      float_utilst float_utils(prop, to_floatbv_type(op.type()));
      return prop.land(
        !float_utils.is_infinity(bv),
        !float_utils.is_NaN(bv));
    }
    else if(op.id() == ID_fixedbv)
      return const_literal(true);
  }
  else if(expr.id()==ID_isinf)
  {
    const auto &op = to_unary_expr(expr).op();
    const bvt &bv = convert_bv(op);

    if(op.type().id() == ID_floatbv)
    {
      float_utilst float_utils(prop, to_floatbv_type(op.type()));
      return float_utils.is_infinity(bv);
    }
    else if(op.type().id() == ID_fixedbv)
      return const_literal(false);
  }
  else if(expr.id()==ID_isnormal)
  {
    const auto &op = to_unary_expr(expr).op();

    if(op.type().id() == ID_floatbv)
    {
      const bvt &bv = convert_bv(op);
      float_utilst float_utils(prop, to_floatbv_type(op.type()));
      return float_utils.is_normal(bv);
    }
    else if(op.type().id() == ID_fixedbv)
      return const_literal(true);
  }
  else if(expr.id() == ID_function_application)
  {
    functions.record(to_function_application_expr(expr));
    return prop.new_variable();
  }

  return SUB::convert_rest(expr);
}

bool boolbvt::boolbv_set_equality_to_true(const equal_exprt &expr)
{
  if(!equality_propagation)
    return true;

  const typet &type = expr.lhs().type();

  if(
    expr.lhs().id() == ID_symbol && type == expr.rhs().type() &&
    type.id() != ID_bool)
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
  bvt bv = prop.new_variables(width);
  return make_bv_expr(type, bv);
}

bool boolbvt::is_unbounded_array(const typet &type) const
{
  if(type.id()!=ID_array)
    return false;

  if(unbounded_array==unbounded_arrayt::U_ALL)
    return true;

  const std::size_t size = boolbv_width(type);
  if(size == 0)
    return true;

  if(unbounded_array==unbounded_arrayt::U_AUTO)
    if(size > MAX_FLATTENED_ARRAY_SIZE)
      return true;

  return false;
}

binding_exprt::variablest boolbvt::fresh_binding(const binding_exprt &binding)
{
  // to ensure freshness of the new identifiers
  scope_counter++;

  binding_exprt::variablest result;
  result.reserve(binding.variables().size());

  for(const auto &binding : binding.variables())
  {
    const auto &old_identifier = binding.get_identifier();

    // produce a new identifier
    const irep_idt new_identifier =
      "boolbvt::scope::" + std::to_string(scope_counter) +
      "::" + id2string(old_identifier);

    result.emplace_back(new_identifier, binding.type());
  }

  return result;
}

void boolbvt::print_assignment(std::ostream &out) const
{
  arrayst::print_assignment(out);
  map.show(out);
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
