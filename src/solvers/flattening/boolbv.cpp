/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/byte_operators.h>
#include <util/config.h>
#include <util/floatbv_expr.h>
#include <util/magic.h>
#include <util/mathematical_expr.h>
#include <util/mp_arith.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/string_constant.h>

#include <solvers/algebraic/groebner.h>
#include <solvers/algebraic/vanishing.h>
#include <solvers/algebraic/poly_extract.h>
#include <solvers/floatbv/float_utils.h>

#include "literal_vector_expr.h"

#include <algorithm>

endianness_mapt boolbvt::endianness_map(const typet &type) const
{
  const bool little_endian =
    config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN;
  return endianness_map(type, little_endian);
}

/// Convert expression to vector of literalts, using an internal
/// cache to speed up conversion if available. Also assert the resultant
/// vector is of a specific size, and freeze any elements if appropriate.
const bvt &boolbvt::convert_bv(
  const exprt &expr,
  std::optional<std::size_t> expected_width)
{
  // check cache first
  std::pair<bv_cachet::iterator, bool> cache_result =
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

exprt boolbvt::handle(const exprt &expr)
{
  if(expr.type().id() == ID_bool)
    return prop_conv_solvert::handle(expr);
  auto bv = convert_bv(expr);
  set_frozen(bv); // for incremental usage
  return literal_vector_exprt{bv, expr.type()};
}

/// Print that the expression of x has failed conversion,
/// then return a vector of x's width.
bvt boolbvt::conversion_failed(const exprt &expr)
{
  ignoring(expr);

  // try to make it free bits
  std::size_t width = boolbv_width(expr.type());
  return prop.new_variables(width);
}

/// Converts an expression into its gate-level representation and returns a
/// vector of literals corresponding to the outputs of the Boolean circuit.
/// \param expr: Expression to convert
/// \return A vector of literals corresponding to the outputs of the Boolean
///   circuit
bvt boolbvt::convert_bitvector(const exprt &expr)
{
  if(expr.is_boolean())
    return {convert(expr)};

  if(expr.id() == ID_index)
    return convert_index(to_index_expr(expr));
  else if(expr.id() == ID_constraint_select_one)
    return convert_constraint_select_one(expr);
  else if(expr.id() == ID_member)
    return convert_member(to_member_expr(expr));
  else if(expr.id() == ID_with)
    return convert_with(to_with_expr(expr));
  else if(expr.id() == ID_update)
    return convert_update(to_update_expr(expr));
  else if(expr.id() == ID_update_bit)
    return convert_update_bit(to_update_bit_expr(expr));
  else if(expr.id() == ID_case)
    return convert_case(to_case_expr(expr));
  else if(expr.id() == ID_cond)
    return convert_cond(to_cond_expr(expr));
  else if(expr.id() == ID_if)
    return convert_if(to_if_expr(expr));
  else if(expr.is_constant())
    return convert_constant(to_constant_expr(expr));
  else if(expr.id() == ID_typecast)
    return convert_bv_typecast(to_typecast_expr(expr));
  else if(expr.id() == ID_symbol)
    return convert_symbol(to_symbol_expr(expr));
  else if(
    expr.id() == ID_plus || expr.id() == ID_minus ||
    expr.id() == "no-overflow-plus" || expr.id() == "no-overflow-minus")
    return convert_add_sub(expr);
  else if(expr.id() == ID_mult)
    return convert_mult(to_mult_expr(expr));
  else if(expr.id() == ID_div)
    return convert_div(to_div_expr(expr));
  else if(expr.id() == ID_mod)
    return convert_mod(to_mod_expr(expr));
  else if(
    expr.id() == ID_shl || expr.id() == ID_ashr || expr.id() == ID_lshr ||
    expr.id() == ID_rol || expr.id() == ID_ror)
    return convert_shift(to_shift_expr(expr));
  else if(
    expr.id() == ID_floatbv_plus || expr.id() == ID_floatbv_minus ||
    expr.id() == ID_floatbv_mult || expr.id() == ID_floatbv_div)
  {
    return convert_floatbv_op(to_ieee_float_op_expr(expr));
  }
  else if(expr.id() == ID_floatbv_fma)
  {
    return convert_floatbv_fma(to_floatbv_fma_expr(expr));
  }
  else if(expr.id() == ID_floatbv_mod)
    return convert_floatbv_mod_rem(to_binary_expr(expr));
  else if(expr.id() == ID_floatbv_rem)
    return convert_floatbv_mod_rem(to_binary_expr(expr));
  else if(expr.id() == ID_floatbv_typecast)
    return convert_floatbv_typecast(to_floatbv_typecast_expr(expr));
  else if(expr.id() == ID_floatbv_round_to_integral)
    return convert_floatbv_round_to_integral(
      to_floatbv_round_to_integral_expr(expr));
  else if(expr.id() == ID_concatenation)
    return convert_concatenation(to_concatenation_expr(expr));
  else if(expr.id() == ID_replication)
    return convert_replication(to_replication_expr(expr));
  else if(expr.id() == ID_extractbits)
    return convert_extractbits(to_extractbits_expr(expr));
  else if(expr.id() == ID_zero_extend)
    return convert_bitvector(to_zero_extend_expr(expr).lower());
  else if(
    expr.id() == ID_bitnot || expr.id() == ID_bitand || expr.id() == ID_bitor ||
    expr.id() == ID_bitxor || expr.id() == ID_bitxnor ||
    expr.id() == ID_bitnor || expr.id() == ID_bitnand)
    return convert_bitwise(expr);
  else if(expr.id() == ID_unary_minus)
    return convert_unary_minus(to_unary_minus_expr(expr));
  else if(expr.id() == ID_unary_plus)
  {
    return convert_bitvector(to_unary_plus_expr(expr).op());
  }
  else if(expr.id() == ID_abs)
    return convert_abs(to_abs_expr(expr));
  else if(expr.id() == ID_bswap)
    return convert_bswap(to_bswap_expr(expr));
  else if(
    expr.id() == ID_byte_extract_little_endian ||
    expr.id() == ID_byte_extract_big_endian)
    return convert_byte_extract(to_byte_extract_expr(expr));
  else if(
    expr.id() == ID_byte_update_little_endian ||
    expr.id() == ID_byte_update_big_endian)
    return convert_byte_update(to_byte_update_expr(expr));
  else if(expr.id() == ID_nondet_symbol || expr.id() == "quant_symbol")
    return convert_symbol(expr);
  else if(expr.id() == ID_struct)
    return convert_struct(to_struct_expr(expr));
  else if(expr.id() == ID_union)
    return convert_union(to_union_expr(expr));
  else if(expr.id() == ID_empty_union)
    return convert_empty_union(to_empty_union_expr(expr));
  else if(expr.id() == ID_string_constant)
    return convert_bitvector(to_string_constant(expr).to_array_expr());
  else if(expr.id() == ID_named_term)
  {
    const auto &named_term_expr = to_named_term_expr(expr);
    set_to_true(equal_exprt(named_term_expr.symbol(), named_term_expr.value()));
    return convert_symbol(named_term_expr.symbol());
  }
  else if(expr.id() == ID_array)
    return convert_array(expr);
  else if(expr.id() == ID_complex)
    return convert_complex(to_complex_expr(expr));
  else if(expr.id() == ID_complex_real)
    return convert_complex_real(to_complex_real_expr(expr));
  else if(expr.id() == ID_complex_imag)
    return convert_complex_imag(to_complex_imag_expr(expr));
  else if(expr.id() == ID_array_comprehension)
    return convert_array_comprehension(to_array_comprehension_expr(expr));
  else if(expr.id() == ID_array_of)
    return convert_array_of(to_array_of_expr(expr));
  else if(expr.id() == ID_let)
    return convert_let(to_let_expr(expr));
  else if(expr.id() == ID_function_application)
    return convert_function_application(to_function_application_expr(expr));
  else if(
    expr.id() == ID_reduction_or || expr.id() == ID_reduction_and ||
    expr.id() == ID_reduction_nor || expr.id() == ID_reduction_nand ||
    expr.id() == ID_reduction_xor || expr.id() == ID_reduction_xnor)
    return convert_bv_reduction(to_unary_expr(expr));
  else if(expr.id() == ID_not)
    return convert_not(to_not_expr(expr));
  else if(expr.id() == ID_power)
    return convert_power(to_power_expr(expr));
  else if(expr.id() == ID_popcount)
    return convert_popcount(to_popcount_expr(expr));
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
  else if(
    const auto overflow_with_result =
      expr_try_dynamic_cast<overflow_result_exprt>(expr))
  {
    return convert_overflow_result(*overflow_with_result);
  }
  else if(expr.id() == ID_find_first_set)
    return convert_bv(simplify_expr(to_find_first_set_expr(expr).lower(), ns));
  else if(expr.id() == ID_literal_vector)
    return to_literal_vector_expr(expr).bv();

  return conversion_failed(expr);
}

bvt boolbvt::convert_array_comprehension(const array_comprehension_exprt &expr)
{
  std::size_t width = boolbv_width(expr.type());

  const exprt &array_size = expr.type().size();

  const auto size = numeric_cast_v<mp_integer>(to_constant_expr(array_size));

  typet counter_type = expr.arg().type();

  bvt bv;
  bv.resize(width);

  for(mp_integer i = 0; i < size; ++i)
  {
    exprt counter = from_integer(i, counter_type);

    exprt body = expr.instantiate({counter});

    const bvt &tmp = convert_bv(body);

    INVARIANT(
      size * tmp.size() == width,
      "total bitvector width shall equal the number of operands times the size "
      "per operand");

    std::size_t offset = numeric_cast_v<std::size_t>(i * tmp.size());

    for(std::size_t j = 0; j < tmp.size(); j++)
      bv[offset + j] = tmp[j];
  }

  return bv;
}

bvt boolbvt::convert_symbol(const exprt &expr)
{
  const typet &type = expr.type();
  std::size_t width = boolbv_width(type);

  const irep_idt &identifier = expr.get(ID_identifier);
  CHECK_RETURN(!identifier.empty());

  bvt bv = map.get_literals(identifier, type, width);

  INVARIANT_WITH_DIAGNOSTICS(
    std::all_of(
      bv.begin(),
      bv.end(),
      [this](const literalt &l)
      { return l.var_no() < prop.no_variables() || l.is_constant(); }),
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
  PRECONDITION(expr.is_boolean());

  if(expr.id() == ID_typecast)
    return convert_typecast(to_typecast_expr(expr));
  else if(expr.id() == ID_equal)
    return convert_equality(to_equal_expr(expr));
  else if(
    expr.id() == ID_verilog_case_equality ||
    expr.id() == ID_verilog_case_inequality)
    return convert_verilog_case_equality(to_binary_relation_expr(expr));
  else if(expr.id() == ID_notequal)
  {
    const auto &notequal_expr = to_notequal_expr(expr);
    return !convert_equality(
      equal_exprt(notequal_expr.lhs(), notequal_expr.rhs()));
  }
  else if(
    expr.id() == ID_ieee_float_equal || expr.id() == ID_ieee_float_notequal)
  {
    return convert_ieee_float_rel(to_binary_relation_expr(expr));
  }
  else if(
    expr.id() == ID_le || expr.id() == ID_ge || expr.id() == ID_lt ||
    expr.id() == ID_gt)
  {
    return convert_bv_rel(to_binary_relation_expr(expr));
  }
  else if(expr.id() == ID_extractbit)
    return convert_extractbit(to_extractbit_expr(expr));
  else if(expr.id() == ID_forall)
    return convert_quantifier(to_quantifier_expr(expr));
  else if(expr.id() == ID_exists)
    return convert_quantifier(to_quantifier_expr(expr));
  else if(expr.id() == ID_let)
  {
    bvt bv = convert_let(to_let_expr(expr));

    DATA_INVARIANT(
      bv.size() == 1, "convert_let must return 1-bit vector for boolean let");

    return bv[0];
  }
  else if(expr.id() == ID_index)
  {
    bvt bv = convert_index(to_index_expr(expr));
    CHECK_RETURN(bv.size() == 1);
    return bv[0];
  }
  else if(expr.id() == ID_member)
  {
    bvt bv = convert_member(to_member_expr(expr));
    CHECK_RETURN(bv.size() == 1);
    return bv[0];
  }
  else if(expr.id() == ID_case)
  {
    bvt bv = convert_case(to_case_expr(expr));
    CHECK_RETURN(bv.size() == 1);
    return bv[0];
  }
  else if(expr.id() == ID_cond)
  {
    bvt bv = convert_cond(to_cond_expr(expr));
    CHECK_RETURN(bv.size() == 1);
    return bv[0];
  }
  else if(expr.id() == ID_sign)
  {
    const auto &op = to_sign_expr(expr).op();
    const bvt &bv = convert_bv(op);
    CHECK_RETURN(!bv.empty());
    const irep_idt type_id = op.type().id();
    if(type_id == ID_signedbv || type_id == ID_fixedbv || type_id == ID_floatbv)
      return bv_utils.sign_bit(bv);
    if(type_id == ID_unsignedbv)
      return const_literal(false);
  }
  else if(
    expr.id() == ID_reduction_or || expr.id() == ID_reduction_and ||
    expr.id() == ID_reduction_nor || expr.id() == ID_reduction_nand ||
    expr.id() == ID_reduction_xor || expr.id() == ID_reduction_xnor)
    return convert_reduction(to_unary_expr(expr));
  else if(expr.id() == ID_onehot)
    return convert_onehot(to_onehot_expr(expr));
  else if(expr.id() == ID_onehot0)
    return convert_onehot(to_onehot0_expr(expr));
  else if(
    const auto binary_overflow =
      expr_try_dynamic_cast<binary_overflow_exprt>(expr))
  {
    return convert_binary_overflow(*binary_overflow);
  }
  else if(
    const auto unary_overflow =
      expr_try_dynamic_cast<unary_overflow_exprt>(expr))
  {
    return convert_unary_overflow(*unary_overflow);
  }
  else if(expr.id() == ID_isnan)
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
  else if(expr.id() == ID_isfinite)
  {
    const auto &op = to_unary_expr(expr).op();
    const bvt &bv = convert_bv(op);

    if(op.type().id() == ID_floatbv)
    {
      float_utilst float_utils(prop, to_floatbv_type(op.type()));
      return prop.land(!float_utils.is_infinity(bv), !float_utils.is_NaN(bv));
    }
    else if(op.type().id() == ID_fixedbv)
      return const_literal(true);
  }
  else if(expr.id() == ID_isinf)
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
  else if(expr.id() == ID_isnormal)
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

    const bvt &bv1 = convert_bv(expr.rhs());

    const irep_idt &identifier = to_symbol_expr(expr.lhs()).identifier();

    map.set_literals(identifier, type, bv1);

    if(freeze_all)
      set_frozen(bv1);

    return false;
  }

  return true;
}

void boolbvt::set_to(const exprt &expr, bool value)
{
  PRECONDITION(expr.is_boolean());

  // Collect polynomial equations for algebraic solving
  if(!algebraic_solved && expr.id() == ID_equal)
  {
    const auto &eq = to_equal_expr(expr);
    auto is_internal = [](const exprt &e)
    {
      return e.id() == ID_symbol &&
             id2string(to_symbol_expr(e).get_identifier()).find("__CPROVER") !=
               std::string::npos;
    };
    if(!is_internal(eq.lhs()) && !is_internal(eq.rhs()))
    {
      if(value)
        algebraic_equalities.push_back(expr);
      else
        algebraic_disequalities.push_back(expr);
    }
  }
  // Also catch not(equal(...)) set to true = disequality
  if(
    !algebraic_solved && expr.id() == ID_not && expr.operands().size() == 1 &&
    expr.operands()[0].id() == ID_equal && value)
  {
    const auto &eq = to_equal_expr(expr.operands()[0]);
    auto is_internal = [](const exprt &e)
    {
      return e.id() == ID_symbol &&
             id2string(to_symbol_expr(e).get_identifier()).find("__CPROVER") !=
               std::string::npos;
    };
    if(!is_internal(eq.lhs()) && !is_internal(eq.rhs()))
    {
      algebraic_disequalities.push_back(expr.operands()[0]);
    }
  }

  // Count symbolic multiplications for adaptive encoding
  expr.visit_pre(
    [this](const exprt &e)
    {
      if(
        e.id() == ID_mult && e.operands().size() == 2 &&
        !e.operands()[0].is_constant() && !e.operands()[1].is_constant())
        ++total_mult_count;
    });

  const auto equal_expr = expr_try_dynamic_cast<equal_exprt>(expr);
  if(value && equal_expr && !boolbv_set_equality_to_true(*equal_expr))
    return;
  SUB::set_to(expr, value);
}

bool boolbvt::is_unbounded_array(const typet &type) const
{
  if(type.id() != ID_array)
    return false;

  if(unbounded_array == unbounded_arrayt::U_ALL)
    return true;

  const auto &size_opt = bv_width.get_width_opt(type);
  if(!size_opt.has_value())
    return true;

  if(unbounded_array == unbounded_arrayt::U_AUTO)
    if(*size_opt > MAX_FLATTENED_ARRAY_SIZE)
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
    const auto &old_identifier = binding.identifier();

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

bool boolbvt::try_algebraic_solve()
{
  if(algebraic_solved)
    return false;
  if(algebraic_disequalities.empty())
    return false;
  // For layer ablation experiments: disable entire algebraic solving
  if(std::getenv("DISABLE_ALGEBRAIC"))
    return false;

  algebraic_solved = true;

  poly_extractort extractor;
  std::vector<polynomialt> equations;

  // Extract polynomial equations from SSA definitions
  for(const auto &eq : algebraic_equalities)
  {
    auto poly = extractor.extract_equation(eq);
    if(poly.has_value() && !poly->is_zero())
      equations.push_back(std::move(*poly));
  }

  // Extract disequalities (negated assertions) via Rabinowitsch trick
  for(const auto &eq : algebraic_disequalities)
  {
    if(eq.id() != ID_equal || eq.operands().size() != 2)
      continue;
    auto lhs = extractor.to_polynomial(to_equal_expr(eq).lhs());
    auto rhs = extractor.to_polynomial(to_equal_expr(eq).rhs());
    if(!lhs || !rhs)
      continue;
    unsigned bw = extractor.get_bitwidth();
    if(bw == 0)
      continue;
    polynomialt diff = *lhs - *rhs;
    std::size_t e_idx = extractor.get_var_index("__rabinowitsch");
    polynomialt e{bw, mp_integer{1}, e_idx};
    polynomialt constraint = (diff * e) - polynomialt{bw, mp_integer{1}};
    constraint.normalize();
    if(!constraint.is_zero())
      equations.push_back(std::move(constraint));
  }

  // Try each disequality independently: if any single disequality
  // is provably UNSAT (regardless of other constraints), the whole
  // formula is UNSAT. This handles cases like overflow_detect where
  // one assertion is non-polynomial but the disequality is polynomial.
  for(const auto &diseq : algebraic_disequalities)
  {
    if(diseq.id() != ID_equal || diseq.operands().size() != 2)
      continue;
    poly_extractort single_extractor;
    auto lhs = single_extractor.to_polynomial(to_equal_expr(diseq).lhs());
    auto rhs = single_extractor.to_polynomial(to_equal_expr(diseq).rhs());
    if(!lhs || !rhs)
      continue;
    unsigned single_bw = single_extractor.get_bitwidth();
    if(single_bw == 0)
      continue;
    polynomialt diff = *lhs - *rhs;

    // Try vanishing polynomial test (complete for polynomial equivalence).
    // Substitute SSA definitions to get the polynomial in input variables.
    {
      std::map<irep_idt, exprt> subst_map;
      for(const auto &eq : algebraic_equalities)
      {
        if(eq.id() == ID_equal)
        {
          const auto &eqe = to_equal_expr(eq);
          if(eqe.lhs().id() == ID_symbol)
            subst_map[to_symbol_expr(eqe.lhs()).get_identifier()] =
              eqe.rhs();
          else if(eqe.rhs().id() == ID_symbol)
            subst_map[to_symbol_expr(eqe.rhs()).get_identifier()] =
              eqe.lhs();
        }
      }

      // Recursively substitute symbols with their definitions
      std::function<void(exprt &)> substitute = [&](exprt &e) {
        for(auto &op : e.operands())
          substitute(op);
        if(e.id() == ID_symbol)
        {
          auto it =
            subst_map.find(to_symbol_expr(e).get_identifier());
          if(it != subst_map.end())
          {
            e = it->second;
            substitute(e); // recurse into the replacement
          }
        }
      };
      exprt expanded = diseq;
      substitute(expanded);

      if(expanded.id() == ID_equal)
      {
        poly_extractort inline_extractor;
        inline_extractor.inline_products = true;
        auto ilhs = inline_extractor.to_polynomial(
          to_equal_expr(expanded).lhs());
        auto irhs = inline_extractor.to_polynomial(
          to_equal_expr(expanded).rhs());
        if(ilhs && irhs)
        {
          polynomialt idiff = *ilhs - *irhs;
          // Build input widths from zero_extend tracking
          std::vector<unsigned> input_widths(
            inline_extractor.var_input_widths.empty()
              ? 0
              : inline_extractor.var_input_widths.rbegin()->first + 1,
            0);
          for(const auto &[var, w] : inline_extractor.var_input_widths)
            input_widths[var] = w;
          const bool van_disabled = std::getenv("DISABLE_VANISHING") != nullptr;
      if(!van_disabled && is_vanishing_polynomial(idiff, input_widths))
          {
            prop.l_set_to_true(const_literal(false));
            return true;
          }
        }
      }
    }

    std::size_t e_idx = single_extractor.get_var_index("__rab");
    polynomialt e_var{single_bw, mp_integer{1}, e_idx};
    polynomialt rab = (diff * e_var) - polynomialt{single_bw, mp_integer{1}};
    rab.normalize();
    if(rab.is_zero())
      continue;

    std::vector<polynomialt> single_eqs;
    // Also extract equalities (SSA definitions) using the same extractor
    // so that define-fun equations are included.
    for(const auto &eq : algebraic_equalities)
    {
      auto poly = single_extractor.extract_equation(eq);
      if(poly.has_value() && !poly->is_zero())
        single_eqs.push_back(std::move(*poly));
    }
    // Add side equations from fresh variable decomposition
    for(auto &se : single_extractor.side_equations)
    {
      se.normalize();
      if(!se.is_zero())
        single_eqs.push_back(std::move(se));
    }
    // Add Rabinowitsch last (ordering matters for Gröbner basis)
    single_eqs.push_back(std::move(rab));

    if(single_eqs.size() >= 2)
    {
      strong_groebner_basist single_gb{100000};
      if(
        single_gb.compute(single_eqs) == strong_groebner_basist::resultt::UNSAT)
      {
        prop.l_set_to_true(const_literal(false));
        return true;
      }
    }
  }

  if(equations.size() + extractor.side_equations.size() < 2)
    return false;

  // IMPORTANT: Equation ordering is critical for Gröbner basis performance.
  // Defining equations (e.g., f0 - a*b = 0) MUST come before the
  // Rabinowitsch equation ((c-d)*e - 1 = 0). With the wrong order
  // (Rabinowitsch first), the algorithm takes 2000x longer because
  // the initial S-polynomials involve the auxiliary Rabinowitsch
  // variable, producing harder intermediate polynomials. With
  // definitions first, the algorithm builds up the ideal incrementally
  // and reduces the Rabinowitsch equation efficiently.
  // The GROEBNER_REVERSE_ORDER env var enables reversed ordering
  // for ablation experiments.
  {
    std::vector<polynomialt> ordered;
    const bool reverse_order = std::getenv("GROEBNER_REVERSE_ORDER") != nullptr;
    if(reverse_order)
    {
      // Wrong order: Rabinowitsch first, then definitions
      for(auto &eq : equations)
        ordered.push_back(std::move(eq));
      for(auto &se : extractor.side_equations)
      {
        se.normalize();
        if(!se.is_zero())
          ordered.push_back(std::move(se));
      }
    }
    else
    {
      // 1. Side equations (definitions from fresh variable decomposition)
      for(auto &se : extractor.side_equations)
      {
        se.normalize();
        if(!se.is_zero())
          ordered.push_back(std::move(se));
      }
      // 2. Main equations (SSA equalities, then Rabinowitsch last)
      for(auto &eq : equations)
        ordered.push_back(std::move(eq));
    }
    equations = std::move(ordered);
  }

  strong_groebner_basist gb{100000};
  auto result = gb.compute(equations);

  if(result == strong_groebner_basist::resultt::UNSAT)
  {
    // Add empty clause to make SAT solver return UNSAT
    prop.l_set_to_true(const_literal(false));
    return true;
  }

  // Level 3: when UNKNOWN, extract candidate assignment and use it
  // to add unit propagation clauses that guide the SAT solver.
  unsigned bw = extractor.get_bitwidth();
  if(bw > 0)
  {
    auto candidate = strong_groebner_basist::extract_candidate(equations, bw);
    if(!candidate.empty())
    {
      const auto &rev_map = extractor.get_reverse_var_map();
      for(const auto &[var_idx, val] : candidate)
      {
        auto name_it = rev_map.find(var_idx);
        if(name_it == rev_map.end())
          continue;

        // Look up the bit-vector for this symbol in boolbvt's cache
        symbol_exprt sym(name_it->second, unsignedbv_typet(bw));
        const bvt &bv = convert_bv(sym);

        // Add implications: for each bit, if the candidate value
        // determines it, add as a soft hint (assumption-gated).
        // We use a gate literal so these can be retracted if wrong.
        literalt gate = prop.new_variable();
        mp_integer v = val;
        for(std::size_t bit = 0; bit < bv.size() && bit < bw; ++bit)
        {
          if(!bv[bit].is_constant())
          {
            literalt expected = (v % 2 != 0) ? bv[bit] : !bv[bit];
            // gate => expected (i.e., !gate OR expected)
            prop.lcnf(!gate, expected);
          }
          v /= 2;
        }
        // The gate is an assumption — if the candidate is wrong,
        // the SAT solver will find a conflict involving the gate
        // and can ignore it.
        algebraic_assumptions.push_back(gate);
      }
    }
  }

  return false;
}
