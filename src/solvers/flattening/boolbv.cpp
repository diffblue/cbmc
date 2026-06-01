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
#include <util/format_expr.h>
#include <util/magic.h>
#include <util/mathematical_expr.h>
#include <util/mp_arith.h>
#include <util/replace_symbol.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/string_constant.h>

#include <solvers/algebraic/groebner.h>
#include <solvers/algebraic/poly_extract.h>
#include <solvers/algebraic/vanishing.h>
#include <solvers/floatbv/float_utils.h>

#include "literal_vector_expr.h"
#include "tseitin_propagation.h"

#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <unordered_set>

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

  // Phase A.2: walk into AND/OR/NOT/LET/IF wrappers to surface
  // equalities for algebraic solving. The direct handlers below
  // catch only top-level equalities; without this walk, benchmarks
  // like cohencu_0/geo3.c_5 (which wrap their polynomial constraints
  // in `(let ... (and ... ...))`) never reach the algebraic solver.
  //
  // The walk respects the env var DISABLE_ALGEBRAIC_TREE_WALK for
  // ablation. The walk is purely additive: it contributes to
  // `algebraic_equalities` / `algebraic_disequalities` but does not
  // skip any of the existing direct handling.
  //
  // PROOF: formal-proofs/AlgebraicTreeWalk.lean::leaf_implied_by_walk.
  if(!algebraic_solved && std::getenv("DISABLE_ALGEBRAIC_TREE_WALK") == nullptr)
  {
    std::size_t leaf_count = 0;
    walk_for_algebraic(expr, value, 0, leaf_count);
  }

  // Item 6 from doc/paper-algebraic/remaining-work.md: detect
  // "clearly non-polynomial" expressions in DISEQUALITIES and skip
  // pushing them to algebraic_disequalities. The narrow definition:
  // contains an extractbits whose lower index is non-zero. The
  // polynomial extractor's `to_polynomial` returns nullopt for
  // these (a single-ring polynomial cannot represent a non-LSB
  // bit slice), so adding such disequalities to
  // algebraic_disequalities costs Buchberger setup time without
  // any chance of refutation.
  //
  // Concrete benefit: synthetic high-half-of-product overflow
  // benchmarks
  // (`(extract 2N-1 N) (bvmul (concat 0 s) (concat 0 t)) != 0`)
  // previously had `algebraic_disequalities` populated, which kept
  // try_algebraic_solve running its predicate-extraction and
  // main_gb setup for ~4 s on a 64-bit example before failing. With
  // the early-out, the same benchmark short-circuits to bit-blasting
  // in 0.02 s.
  //
  // We do NOT apply this guard to algebraic_equalities. The
  // Tseitin propagator (Phase 2.6) uses equalities containing
  // extractbits on boolean atoms (e.g.\ `(= bool_var ((_ extract 0 0)
  // bv_var))`) for forward and backward chain propagation; such
  // equalities are useful for Tseitin even though the polynomial
  // extractor's `to_polynomial` returns nullopt for them.
  std::function<bool(const exprt &)> contains_high_extract =
    [&contains_high_extract](const exprt &e) -> bool
  {
    if(e.id() == ID_extractbits && e.operands().size() == 2)
    {
      auto idx = numeric_cast<mp_integer>(e.operands()[1]);
      if(idx.has_value() && *idx > 0)
        return true;
    }
    for(const auto &op : e.operands())
      if(contains_high_extract(op))
        return true;
    return false;
  };
  auto is_diseq_polynomial_friendly =
    [&contains_high_extract](const exprt &lhs, const exprt &rhs) -> bool
  { return !contains_high_extract(lhs) && !contains_high_extract(rhs); };

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
      {
        // Equalities: push regardless of polynomial-friendliness;
        // Tseitin propagator can use boolean-atom equalities even
        // when the polynomial extractor cannot.
        algebraic_equalities.push_back(expr);
      }
      else if(is_diseq_polynomial_friendly(eq.lhs(), eq.rhs()))
      {
        algebraic_disequalities.push_back(expr);
      }
    }
  }
  // Also catch (notequal a b) set to true and (notequal a b) set to
  // false: SMT-LIB's `distinct` parses as `notequal_exprt`, which is
  // semantically `not (equal)`. We translate to the same algebraic
  // equality / disequality bucket as the `equal_exprt` path above.
  if(!algebraic_solved && expr.id() == ID_notequal)
  {
    const auto &neq = to_notequal_expr(expr);
    auto is_internal = [](const exprt &e)
    {
      return e.id() == ID_symbol &&
             id2string(to_symbol_expr(e).get_identifier()).find("__CPROVER") !=
               std::string::npos;
    };
    if(!is_internal(neq.lhs()) && !is_internal(neq.rhs()))
    {
      // (notequal a b) is the negation of (equal a b).
      auto as_equal = equal_exprt(neq.lhs(), neq.rhs());
      if(value && is_diseq_polynomial_friendly(neq.lhs(), neq.rhs()))
      {
        algebraic_disequalities.push_back(as_equal);
      }
      else if(!value)
      {
        algebraic_equalities.push_back(as_equal);
      }
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
    if(
      !is_internal(eq.lhs()) && !is_internal(eq.rhs()) &&
      is_diseq_polynomial_friendly(eq.lhs(), eq.rhs()))
    {
      algebraic_disequalities.push_back(expr.operands()[0]);
    }
  }

  // Disjunction of disequalities, set to true.
  // Pattern: (or (distinct e1 e2) (distinct e3 e4) ... (distinct e_{2k-1} e_{2k}))
  // SMT-LIB's (distinct a b) becomes ID_notequal; (not (= a b)) is also
  // accepted. The whole disjunction is UNSAT iff every branch is UNSAT
  // (each branch refuted independently via Rabinowitsch + Buchberger).
  // Branches that don't pattern-match (e.g., non-disequality predicates,
  // expressions involving __CPROVER internals) cause the disjunction to
  // be left to bit-blasting.
  if(
    !algebraic_solved && expr.id() == ID_or && value &&
    expr.operands().size() >= 2)
  {
    auto is_internal = [](const exprt &e)
    {
      return e.id() == ID_symbol &&
             id2string(to_symbol_expr(e).get_identifier()).find("__CPROVER") !=
               std::string::npos;
    };
    std::vector<exprt> branch_diseqs;
    bool all_diseqs = true;
    for(const auto &op : expr.operands())
    {
      // Two equivalent shapes: (distinct a b) → notequal_exprt with
      // id ID_notequal; (not (= a b)) → not_exprt over equal_exprt.
      if(
        op.id() == ID_notequal && op.operands().size() == 2 &&
        !is_internal(op.operands()[0]) && !is_internal(op.operands()[1]))
      {
        // Construct an equal_exprt (the diseq's negation), the same
        // form algebraic_disequalities holds: this lets us reuse the
        // same per-disequality processing pipeline.
        branch_diseqs.push_back(
          equal_exprt{op.operands()[0], op.operands()[1]});
      }
      else if(
        op.id() == ID_not && op.operands().size() == 1 &&
        op.operands()[0].id() == ID_equal &&
        op.operands()[0].operands().size() == 2 &&
        !is_internal(op.operands()[0].operands()[0]) &&
        !is_internal(op.operands()[0].operands()[1]))
      {
        branch_diseqs.push_back(op.operands()[0]);
      }
      else
      {
        all_diseqs = false;
        break;
      }
    }
    if(all_diseqs && !branch_diseqs.empty())
    {
      algebraic_disjunctive_disequalities.push_back(std::move(branch_diseqs));
    }
  }

  // Universal-relational predicates (Re 4 sub-goal 6):
  // recognise asserted bvult/bvule (and their negations) when the
  // operands are not __CPROVER internals. The polynomial encoding
  // is performed by poly_extractort::extract_predicate at the
  // Buchberger-setup site, alongside extract_equation for the
  // equational facts.
  //
  // We also handle (not (bvult ...)) / (not (bvule ...)) set to
  // true, which is equivalent to bvuge / bvugt set to true.
  auto is_relational = [](const irep_idt &id)
  { return id == ID_lt || id == ID_le || id == ID_gt || id == ID_ge; };
  auto is_internal_op = [](const exprt &e)
  {
    return e.id() == ID_symbol &&
           id2string(to_symbol_expr(e).get_identifier()).find("__CPROVER") !=
             std::string::npos;
  };
  // Phase A.3 fast-path helper for "x is unequal to a constant"
  // patterns. Returns true iff the predicate (id, lhs, rhs, v) is
  // logically equivalent to `x != C` for C in {0, ~0}, in which
  // case it pushes `(= x C)` to nonzero_pending (deferred; promoted
  // to algebraic_disequalities by try_algebraic_solve only when the
  // formula contains bvudiv/bvurem, to avoid SAT-benchmark
  // worklist flooding on Sage2-style inputs).
  //
  // Patterns recognised:
  //
  //   x != 0:
  //     bvult 0 x         -> ID_ge, lhs=x, rhs=1, v=true
  //     bvule 1 x         -> ID_ge, lhs=x, rhs=1, v=true
  //     0 < x  (raw form) -> ID_lt, lhs=0, v=true
  //     1 <= x (raw form) -> ID_le, lhs=1, v=true
  //
  //   x != ~0 (NEW in this extension):
  //     bvult x ~0        -> ID_ge, lhs=x, rhs=~0, v=false
  //                          (parses as not (x >= ~0))
  //     bvule x ~0-1      -> ID_le, lhs=x, rhs=~0-1, v=true
  //     x < ~0 (raw)      -> ID_lt, lhs=x, rhs=~0, v=true
  //
  // PROOF: BvDivPolyEncoding.lean::NonzeroFastPath::
  //        bvult_zero_iff_ne_zero, bvuge_one_iff_ne_zero.
  //        Symmetric reasoning applies to x != ~0 by the
  //        bijection x <-> ~x in unsigned bit-vector semantics.
  auto try_nonzero_fast_path =
    [&](const irep_idt &id, const exprt &lhs, const exprt &rhs, bool v) -> bool
  {
    if(std::getenv("DISABLE_NONZERO_FAST_PATH") != nullptr)
      return false;
    const bool unsigned_op =
      lhs.type().id() == ID_unsignedbv && rhs.type().id() == ID_unsignedbv;
    if(!unsigned_op)
      return false;
    const std::size_t d = to_unsignedbv_type(lhs.type()).get_width();
    if(d == 0)
      return false;
    const mp_integer two_d = power(mp_integer{2}, mp_integer{d});
    const mp_integer max_d = two_d - 1;
    auto is_const_eq = [](const exprt &e, const mp_integer &val) -> bool
    {
      if(!e.is_constant())
        return false;
      auto vv = numeric_cast<mp_integer>(e);
      return vv.has_value() && *vv == val;
    };
    const exprt *x_side = nullptr;
    mp_integer excluded{0};
    if(id == ID_ge && v && is_const_eq(rhs, mp_integer{1}))
    {
      x_side = &lhs;
      excluded = 0;
    }
    else if(id == ID_le && v && is_const_eq(lhs, mp_integer{1}))
    {
      x_side = &rhs;
      excluded = 0;
    }
    else if(id == ID_lt && v && is_const_eq(lhs, mp_integer{0}))
    {
      x_side = &rhs;
      excluded = 0;
    }
    else if(id == ID_ge && !v && is_const_eq(rhs, max_d))
    {
      // NOT (x >= ~0)  ⇒  x < ~0  ⇒  x != ~0
      x_side = &lhs;
      excluded = max_d;
    }
    else if(id == ID_le && v && is_const_eq(rhs, max_d - 1))
    {
      x_side = &lhs;
      excluded = max_d;
    }
    else if(id == ID_lt && v && is_const_eq(rhs, max_d))
    {
      x_side = &lhs;
      excluded = max_d;
    }
    if(x_side == nullptr || is_internal_op(*x_side))
      return false;
    nonzero_pending.push_back(
      equal_exprt{*x_side, from_integer(excluded, x_side->type())});
    return true;
  };

  if(!algebraic_solved && is_relational(expr.id()))
  {
    if(
      expr.operands().size() == 2 && !is_internal_op(expr.operands()[0]) &&
      !is_internal_op(expr.operands()[1]))
    {
      const bool fast_path_fired = try_nonzero_fast_path(
        expr.id(), expr.operands()[0], expr.operands()[1], value);
      if(!fast_path_fired)
        algebraic_predicates.emplace_back(expr, value);
    }
  }
  if(
    !algebraic_solved && expr.id() == ID_not && expr.operands().size() == 1 &&
    value && is_relational(expr.operands()[0].id()))
  {
    const exprt &inner = expr.operands()[0];
    if(
      inner.operands().size() == 2 && !is_internal_op(inner.operands()[0]) &&
      !is_internal_op(inner.operands()[1]))
    {
      // The not-relational form: NOT (id lhs rhs) is logically
      // equivalent to (id lhs rhs) with value=false. Routed
      // through the same fast-path detector so x != ~0 patterns
      // (which the parser normalises to NOT (x >= ~0)) are caught.
      const bool fast_path_fired = try_nonzero_fast_path(
        inner.id(), inner.operands()[0], inner.operands()[1], false);
      if(!fast_path_fired)
        algebraic_predicates.emplace_back(inner, false);
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

  // Memory-efficient extraction (Re 4 sub-goal 7): defer bit-blasting
  // of SSA equalities until after try_algebraic_solve runs. If the
  // algebraic procedure refutes, the bit-blasting work is skipped
  // entirely. If it does not, the queue is replayed in
  // finish_eager_conversion, recovering identical behaviour.
  //
  // On by default. Set DISABLE_DEFER_BITBLAST=1 to opt out for ablation
  // experiments. See doc/paper-algebraic/paper.tex §4.3 for the SABER
  // empirical impact (100--165× memory reduction).
  if(
    std::getenv("DISABLE_DEFER_BITBLAST") == nullptr &&
    (expr.id() == ID_equal || expr.id() == ID_notequal))
  {
    auto is_internal = [](const exprt &e)
    {
      return e.id() == ID_symbol &&
             id2string(to_symbol_expr(e).get_identifier()).find("__CPROVER") !=
               std::string::npos;
    };
    if(
      expr.operands().size() == 2 && !is_internal(expr.operands()[0]) &&
      !is_internal(expr.operands()[1]))
    {
      deferred_assertions.emplace_back(expr, value);
      return;
    }
  }
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

// PROOF: formal-proofs/AlgebraicTreeWalk.lean::leaf_implied_by_walk
//        Soundness: every leaf collected by walk_for_algebraic is
//        a logical consequence of the parent assertion (expr, value).
//        The walk descends through AND (with value=true), OR (with
//        value=false, by De Morgan), NOT (flipping polarity), LET
//        (inlining the binding), and IF (recognising the IF-rebuild
//        pattern). For each operation, the leaves collected from the
//        children are implied by the parent.
// PROOF: formal-proofs/AlgebraicTreeWalk.lean::if_rebuild_equivalence
//        Soundness of the IF-rebuild step: (if c (= sym A) (= sym B))
//        is equivalent to (= sym (if c A B)) when A and B have the
//        same type. The rebuilt equality is in the same ideal as
//        the original IF expression at depth 0 (since we collected
//        IT instead of recursing).
//   ASSUMES: each leaf is a literal equality/disequality, not
//            re-extracted into a polynomial twice. This is enforced
//            by the bvmul-presence gate (non-IF leaves) and the
//            cumulative leaf cap.
//   MAINTAINED BY: the depth/leaf/total bounds and the polarity
//            tracking through wrappers.
void boolbvt::walk_for_algebraic(
  const exprt &expr,
  bool value,
  std::size_t depth,
  std::size_t &leaf_count)
{
  // Bounds.
  static constexpr std::size_t tree_walk_max_depth = 100;
  static constexpr std::size_t tree_walk_max_leaves = 50;
  static constexpr std::size_t tree_walk_max_total = 200;
  static constexpr std::size_t tree_walk_max_body = 500;

  if(depth > tree_walk_max_depth)
    return;
  if(leaf_count > tree_walk_max_leaves)
    return;
  if(
    algebraic_equalities.size() + algebraic_disequalities.size() >
    tree_walk_max_total)
    return;

  if(!expr.is_boolean())
    return;

  auto is_internal = [](const exprt &e)
  {
    return e.id() == ID_symbol &&
           id2string(to_symbol_expr(e).get_identifier()).find("__CPROVER") !=
             std::string::npos;
  };

  // AND with value=true: every conjunct must hold.
  // OR with value=false: every disjunct must be false (De Morgan).
  if(expr.id() == ID_and && value)
  {
    for(const auto &op : expr.operands())
      walk_for_algebraic(op, true, depth + 1, leaf_count);
    return;
  }
  if(expr.id() == ID_or && !value)
  {
    for(const auto &op : expr.operands())
      walk_for_algebraic(op, false, depth + 1, leaf_count);
    return;
  }

  // NOT flips polarity.
  if(expr.id() == ID_not && expr.operands().size() == 1)
  {
    walk_for_algebraic(expr.operands()[0], !value, depth + 1, leaf_count);
    return;
  }

  // LET: inline the binding (size-bounded), then walk into the body.
  // We use replace_symbolt to substitute let-bound variables with
  // their values in the body. The body-size bound prevents
  // pathological inlining on deeply-nested lets.
  if(
    expr.id() == ID_let && expr.operands().size() >= 2 &&
    can_cast_expr<let_exprt>(expr))
  {
    const auto &le = to_let_expr(expr);
    // Approximate body size by structural depth count (cheap).
    std::size_t body_size = 0;
    le.where().visit_pre([&](const exprt &) { ++body_size; });
    if(body_size > tree_walk_max_body)
      return;
    replace_symbolt rs;
    for(std::size_t i = 0; i < le.binding().variables().size(); ++i)
      rs.set(le.binding().variables()[i], le.values()[i]);
    exprt body = le.where();
    rs(body);
    walk_for_algebraic(body, value, depth + 1, leaf_count);
    return;
  }

  // IF-rebuild: (if c (= sym A) (= sym B)) with value=true →
  // (= sym (if c A B)). This is logically equivalent and exposes
  // the polynomial structure that Phase 2.5's push-through-ite
  // could not always normalise on its own (it requires both
  // branches to have the same shape).
  //
  // We accept any of the four orderings of (sym, value) in the
  // sub-equalities: (= sym A)/(= A sym) on each side.
  if(
    expr.id() == ID_if && expr.operands().size() == 3 && value &&
    can_cast_expr<if_exprt>(expr))
  {
    const auto &ie = to_if_expr(expr);
    const exprt &t = ie.true_case();
    const exprt &f = ie.false_case();
    if(
      t.id() == ID_equal && f.id() == ID_equal && t.operands().size() == 2 &&
      f.operands().size() == 2)
    {
      auto try_rebuild =
        [&](const exprt &sym, const exprt &t_val, const exprt &f_val) -> bool
      {
        if(t_val.type() != f_val.type())
          return false;
        if(sym.type() != t_val.type())
          return false;
        if(is_internal(sym))
          return false;
        // Skip if either value involves an internal __CPROVER ref.
        // These tend to produce noisy synthetic equalities.
        if(is_internal(t_val) || is_internal(f_val))
          return false;
        equal_exprt rebuilt{sym, if_exprt{ie.cond(), t_val, f_val}};
        algebraic_equalities.push_back(std::move(rebuilt));
        ++leaf_count;
        return true;
      };
      // Try matching: t.lhs == f.lhs (sym at lhs in both)
      if(t.operands()[0] == f.operands()[0])
      {
        if(try_rebuild(t.operands()[0], t.operands()[1], f.operands()[1]))
          return;
      }
      // sym at rhs in both
      if(t.operands()[1] == f.operands()[1])
      {
        if(try_rebuild(t.operands()[1], t.operands()[0], f.operands()[0]))
          return;
      }
      // Mixed orderings: sym lhs in t, rhs in f
      if(t.operands()[0] == f.operands()[1])
      {
        if(try_rebuild(t.operands()[0], t.operands()[1], f.operands()[0]))
          return;
      }
      // sym rhs in t, lhs in f
      if(t.operands()[1] == f.operands()[0])
      {
        if(try_rebuild(t.operands()[1], t.operands()[0], f.operands()[1]))
          return;
      }
    }
    return;
  }

  // Leaves at depth > 0: equality/disequality buried under wrappers.
  // (At depth 0 the existing direct handlers in set_to fire, so we
  // skip to avoid double-counting.)
  if(depth == 0)
    return;

  // Helper: does the expression contain ID_mult anywhere?
  // Used to gate non-IF-rebuild leaves: the walk ONLY collects
  // leaves whose operands include a multiplication, since algebraic
  // refutation requires polynomial structure. SAGE/SPEAR-style
  // benchmarks have many shift-and-or boolean equalities buried
  // in ANDs that flooded the algebraic worklist in Phase 2.7's
  // initial attempt.
  std::function<bool(const exprt &)> contains_mult =
    [&contains_mult](const exprt &e) -> bool
  {
    if(e.id() == ID_mult)
      return true;
    for(const auto &op : e.operands())
      if(contains_mult(op))
        return true;
    return false;
  };

  // Item 6: skip leaves whose operands contain a non-zero-LO
  // extractbits, but ONLY for disequalities. The polynomial
  // extractor's `to_polynomial` returns nullopt for such
  // expressions, so they can't drive UNSAT refutation. Equalities,
  // by contrast, are useful to the Tseitin propagator (Phase 2.6)
  // even when not directly polynomial.
  std::function<bool(const exprt &)> contains_high_extract =
    [&contains_high_extract](const exprt &e) -> bool
  {
    if(e.id() == ID_extractbits && e.operands().size() == 2)
    {
      auto idx = numeric_cast<mp_integer>(e.operands()[1]);
      if(idx.has_value() && *idx > 0)
        return true;
    }
    for(const auto &op : e.operands())
      if(contains_high_extract(op))
        return true;
    return false;
  };

  if(expr.id() == ID_equal && expr.operands().size() == 2)
  {
    if(is_internal(expr.operands()[0]) || is_internal(expr.operands()[1]))
      return;
    if(!contains_mult(expr))
      return;
    if(value)
    {
      // Equalities: push regardless of polynomial-friendliness
      // (Tseitin can use them).
      algebraic_equalities.push_back(expr);
    }
    else
    {
      // Disequalities: skip non-polynomial slices to avoid futile
      // Buchberger setup.
      if(contains_high_extract(expr))
        return;
      algebraic_disequalities.push_back(expr);
    }
    ++leaf_count;
    return;
  }
  if(expr.id() == ID_notequal && expr.operands().size() == 2)
  {
    const auto &ne = to_notequal_expr(expr);
    if(is_internal(ne.lhs()) || is_internal(ne.rhs()))
      return;
    equal_exprt as_eq{ne.lhs(), ne.rhs()};
    if(!contains_mult(as_eq))
      return;
    if(value)
    {
      // (distinct a b) set to true ⇒ disequality on (= a b).
      // Apply the polynomial-friendly guard.
      if(contains_high_extract(as_eq))
        return;
      algebraic_disequalities.push_back(std::move(as_eq));
    }
    else
    {
      // (distinct a b) set to false ⇒ equality (= a b).
      // No guard (Tseitin can use it).
      algebraic_equalities.push_back(std::move(as_eq));
    }
    ++leaf_count;
    return;
  }
  // Other leaf shapes: ignore (not within Plan A scope).
}

// PROOF: formal-proofs/Defer.lean::defer_replay_equivalence
//        Soundness: deferring SSA equality bit-blasting and
//        replaying-on-non-refutation is semantically equivalent
//        to the eager bit-blasting path. Proven by induction on
//        the assertion list using `defer_finish_eq_eager_finish`
//        (formerly an axiom; now a theorem in the concrete
//        set-based abstract model of `SolverState`). The
//        commutation lemma `finish_eager_commutes` is similarly
//        a theorem rather than an axiom. See
//        `finish_eager_conversion` in boolbv.h for the call site.
// PROOF: formal-proofs/Defer.lean::defer_verdict_equivalence
//        Corollary: not just states but verdicts (SAT/UNSAT
//        decisions) agree between deferred and eager paths.
//        This is what users actually observe.
// PROOF: formal-proofs/Defer.lean::defer_verdict_from_empty
//        Corollary: starting from the empty solver state, the
//        deferred-then-replayed verdict equals the eager verdict.
//        This matches the actual call pattern in the implementation.
// PROOF: formal-proofs/StrongGB.lean::two_trick_unsat_sound
//        Soundness: when this function returns true, the SAT
//        propagator has been forced to UNSAT via the algebraic
//        refutation chain.
//   ASSUMES: each algebraic refutation step produces a polynomial
//            that is in the ideal generated by the input equations.
//   MAINTAINED BY: the helper functions (s_polynomial, strong_reduce,
//            reduce_by_basis) all preserve ideal membership; the
//            final UNSAT trigger requires an odd constant in the
//            ideal, which by has_constant + ZMod.isUnit_of_odd_nat
//            forces ideal = ⊤, i.e., no model exists.
bool boolbvt::try_algebraic_solve()
{
  if(algebraic_solved)
    return false;

  // For layer ablation experiments: disable entire algebraic solving
  if(std::getenv("DISABLE_ALGEBRAIC"))
    return false;

  // Item 13 / Bug A (soundness): refuse (dis)equalities that widen a
  // DEFINED INTERMEDIATE across a typecast.
  //
  // C integer promotion encodes e.g.\ `(a*b)*c` on 9-bit operands as
  //   cast(ab, signedbv[32]) * cast(c, signedbv[32])
  // where `ab` is the SSA symbol defined by `ab = a*b` (truncated to
  // 9 bits). The polynomial extractor reasons in a single ZMod(2^w)
  // ring; pinning that ring to 9 bits (from the defining equations)
  // and then absorbing the widening cast silently treats `ab` as the
  // exact 9-bit product inside a 32-bit multiplication. That is
  // unsound: `ab = a*b mod 2^9`, so `ab*c` at 32 bits is NOT
  // `a*b*c` (the high bits dropped by the 9-bit truncation matter at
  // 32 bits). The associativity assertion is then wrongly "proved".
  //
  // We detect the unsound shape precisely — a widening typecast of a
  // symbol that is a defined intermediate (the bare-symbol side of an
  // algebraic equality whose other side is a non-trivial expression)
  // — and drop the offending (dis)equality so the formula falls back
  // to bit-blasting. This preserves the sound cases: widening a
  // primary INPUT (e.g.\ mul_overflow's `cast(a,32)*cast(b,32)` where
  // a, b have no defining equation) is a faithful zero/sign extension
  // and is kept; SMT-LIB benchmarks carry no ID_typecast at all and
  // are unaffected.
  {
    std::set<irep_idt> defined_syms;
    auto note_def = [&defined_syms](const exprt &lhs, const exprt &rhs)
    {
      if(
        lhs.id() == ID_symbol && rhs.id() != ID_symbol &&
        rhs.id() != ID_constant)
        defined_syms.insert(to_symbol_expr(lhs).get_identifier());
    };
    for(const auto &eq : algebraic_equalities)
      if(eq.id() == ID_equal && eq.operands().size() == 2)
      {
        note_def(eq.operands()[0], eq.operands()[1]);
        note_def(eq.operands()[1], eq.operands()[0]);
      }

    auto bv_width = [](const typet &t) -> unsigned
    {
      if(const auto bv = type_try_dynamic_cast<bitvector_typet>(t))
        return bv->get_width();
      return 0;
    };
    // A widening cast of a defined intermediate is unsound ONLY when
    // its (wide) result is consumed by wide arithmetic. If the
    // widening is immediately re-narrowed (e.g.\ matrix_mul's
    // `cast(cast(c00, 32), 8)`), the net value is the original
    // narrow value and the algebra is faithful. So we fire only when
    // a widening `cast(defined_sym, W)` appears as a DIRECT operand
    // of an arithmetic node (* + - unary-). In assoc the mult
    // `cast(ab,32) * cast(c,32)` matches (ab is defined); in
    // matrix_mul the widening cast is the operand of the narrowing
    // outer cast, not of the `+`, so it does not match.
    auto is_widening_cast_of_defined = [&](const exprt &x) -> bool
    {
      if(x.id() != ID_typecast || x.operands().size() != 1)
        return false;
      const exprt &op = to_typecast_expr(x).op();
      if(op.id() != ID_symbol)
        return false;
      if(!defined_syms.count(to_symbol_expr(op).get_identifier()))
        return false;
      const unsigned out_w = bv_width(x.type());
      const unsigned in_w = bv_width(op.type());
      return in_w != 0 && out_w > in_w;
    };
    auto widens_defined = [&](const exprt &e) -> bool
    {
      bool found = false;
      e.visit_pre(
        [&](const exprt &x)
        {
          if(
            x.id() != ID_mult && x.id() != ID_plus && x.id() != ID_minus &&
            x.id() != ID_unary_minus)
            return;
          for(const auto &op : x.operands())
            if(is_widening_cast_of_defined(op))
              found = true;
        });
      return found;
    };
    auto drop_if = [&](std::vector<exprt> &v)
    { v.erase(std::remove_if(v.begin(), v.end(), widens_defined), v.end()); };
    drop_if(algebraic_equalities);
    drop_if(algebraic_disequalities);
  }

  // Item 13 / Bug B (soundness): do not refute a zero-divisor system.
  //
  // A disequality `x != 0` is encoded for refutation via the
  // Rabinowitsch trick as `x*e - 1 = 0`, which asserts that x is a
  // UNIT. Over a field that is equivalent to `x != 0`, but over
  // ZMod(2^d) it is strictly stronger: a non-zero element need not be
  // invertible (e.g.\ 16 is non-zero but 16*e = 1 is unsatisfiable
  // mod 256). Consequently the refutation can wrongly conclude UNSAT
  // for a system that is in fact SAT via zero divisors, e.g.
  //   { a*b = 0, a != 0, b != 0 }
  // which holds for a = b = 16 over ZMod(2^8). Reporting UNSAT here
  // makes the solver claim a property holds when it does not.
  //
  // We detect exactly this shape — a product constrained to zero
  // whose two factors are each separately constrained to be non-zero
  // — and skip algebraic solving (fall back to bit-blasting, which
  // models zero divisors correctly). Genuinely-unsat refutations
  // (e.g.\ cohencu) carry no such pattern and are unaffected.
  {
    std::function<const exprt &(const exprt &)> strip_casts =
      [&strip_casts](const exprt &e) -> const exprt &
    {
      if(e.id() == ID_typecast && e.operands().size() == 1)
        return strip_casts(to_typecast_expr(e).op());
      return e;
    };
    auto is_zero_const = [&](const exprt &e)
    {
      const exprt &s = strip_casts(e);
      if(s.id() != ID_constant)
        return false;
      mp_integer v;
      return !to_integer(to_constant_expr(s), v) && v == 0;
    };
    // Symbols asserted non-zero (disequalities store equal(X, 0)).
    std::set<irep_idt> nonzero;
    for(const auto &d : algebraic_disequalities)
    {
      if(d.id() != ID_equal || d.operands().size() != 2)
        continue;
      const exprt *other = nullptr;
      if(is_zero_const(d.operands()[0]))
        other = &d.operands()[1];
      else if(is_zero_const(d.operands()[1]))
        other = &d.operands()[0];
      if(other)
      {
        const exprt &s = strip_casts(*other);
        if(s.id() == ID_symbol)
          nonzero.insert(to_symbol_expr(s).get_identifier());
      }
    }
    // SSA definitions: symbol -> defining expression.
    std::map<irep_idt, exprt> def;
    for(const auto &eq : algebraic_equalities)
    {
      if(eq.id() != ID_equal || eq.operands().size() != 2)
        continue;
      const exprt &l = strip_casts(eq.operands()[0]);
      const exprt &r = strip_casts(eq.operands()[1]);
      if(l.id() == ID_symbol && r.id() != ID_symbol)
        def.emplace(to_symbol_expr(l).get_identifier(), r);
      else if(r.id() == ID_symbol && l.id() != ID_symbol)
        def.emplace(to_symbol_expr(r).get_identifier(), l);
    }
    // Both factors of a product separately non-zero?
    auto both_factors_nonzero = [&](const exprt &prod) -> bool
    {
      const exprt &p = strip_casts(prod);
      if(p.id() != ID_mult || p.operands().size() != 2)
        return false;
      const exprt &f0 = strip_casts(p.operands()[0]);
      const exprt &f1 = strip_casts(p.operands()[1]);
      return f0.id() == ID_symbol && f1.id() == ID_symbol &&
             nonzero.count(to_symbol_expr(f0).get_identifier()) &&
             nonzero.count(to_symbol_expr(f1).get_identifier());
    };
    // A product (directly, or via an SSA symbol) is constrained to 0.
    bool zero_divisor = false;
    for(const auto &eq : algebraic_equalities)
    {
      if(eq.id() != ID_equal || eq.operands().size() != 2)
        continue;
      const exprt *nz = nullptr;
      if(is_zero_const(eq.operands()[0]))
        nz = &eq.operands()[1];
      else if(is_zero_const(eq.operands()[1]))
        nz = &eq.operands()[0];
      if(!nz)
        continue;
      const exprt &z = strip_casts(*nz);
      if(both_factors_nonzero(z))
        zero_divisor = true;
      else if(z.id() == ID_symbol)
      {
        auto it = def.find(to_symbol_expr(z).get_identifier());
        if(it != def.end() && both_factors_nonzero(it->second))
          zero_divisor = true;
      }
    }
    if(zero_divisor)
      return false; // unsound to refute; defer to bit-blasting
  }

  // Phase A.3: promote `x != 0` fast-path disequalities into
  // algebraic_disequalities ONLY when the formula contains a
  // bvudiv or bvurem somewhere. Without this gate, SAT benchmarks
  // with many bvult predicates and no division (e.g.,
  // Sage2_bench_15251/17485, with 218 / 182 bvult occurrences)
  // would suffer because each added disequality runs an entire
  // per-disequality Buchberger iteration without contributing to
  // the eventual SAT verdict.
  //
  // The gate fires exactly when the formula contains division —
  // the only case where the polynomial encoding's `q*t + r - s = 0`
  // side equation makes the `x != 0` constraint relevant for
  // refutation.
  //
  // PROOF: the disequality `(= x 0)` is a logical consequence of
  //        the asserted predicate (`bvult 0 x` / `bvule 1 x` /
  //        `NOT bvule x 0`), so promoting it preserves logical
  //        equivalence regardless of whether bvudiv/bvurem is
  //        present.
  if(!nonzero_pending.empty())
  {
    bool has_div = false;
    auto contains_div = [&has_div](const exprt &e)
    {
      e.visit_pre(
        [&has_div](const exprt &x)
        {
          if(x.id() == ID_div || x.id() == ID_mod)
            has_div = true;
        });
    };
    for(const auto &eq : algebraic_equalities)
      contains_div(eq);
    for(const auto &eq : algebraic_disequalities)
      contains_div(eq);
    if(has_div)
    {
      for(auto &diseq : nonzero_pending)
        algebraic_disequalities.push_back(std::move(diseq));
    }
    nonzero_pending.clear();
  }

  // Phase A.2 case-elimination for IF-rebuild equalities.
  //
  // When the boolean tree walk produces `sym = (if c A B)` with A
  // and B distinct constants, AND there is a disequality `sym = A`
  // (set to false), we can derive that `c` must be false: the true
  // branch (sym = A) contradicts the disequality, so the false
  // branch (sym = B) must hold, which requires c to be false.
  // Symmetrically, a disequality `sym = B` forces c to be true.
  //
  // If c is itself an equality `(= e f)`, emit the corresponding
  // (dis)equality on (e, f). This bridges the IF-rebuild equality
  // (which the polynomial extractor would otherwise drop, since it
  // contains an ITE) to the polynomial system that needs e ≠ f or
  // e = f.
  //
  // Concrete benchmarks where this fires: cohencu_0/1/2/3 in the
  // SMT-COMP sample. There assert 1 has the form
  //   (if (= bvadd(6,6n) z) (= sym 1) (= sym 0))
  // and assert 3 has the form (not (= 1 sym)). The walk's
  // IF-rebuild produces (= sym (if c 1 0)). The case-elimination
  // here detects the disequality on sym matches the constant 1
  // branch, and emits (= bvadd(6,6n) z) as a disequality. Combined
  // with the polynomial equations from assert 2, Buchberger refutes.
  //
  // PROOF: by case analysis on the IF condition c.
  // - If c, then sym = A by the IF equality, contradicting sym ≠ A.
  //   So ¬c.
  // - If ¬c, then sym = B by the IF equality, consistent with
  //   sym ≠ A (provided A ≠ B, which we check).
  // The emitted (dis)equality on c is a valid logical consequence.
  if(std::getenv("DISABLE_IF_CASE_ELIM") == nullptr)
  {
    auto exprs_equal = [](const exprt &a, const exprt &b) { return a == b; };
    auto extract_constant_int = [](const exprt &e, mp_integer &out) -> bool
    {
      if(e.id() != ID_constant)
        return false;
      return !to_integer(to_constant_expr(e), out);
    };
    std::vector<exprt> case_elim_eqs;
    std::vector<exprt> case_elim_diseqs;
    for(const auto &eq : algebraic_equalities)
    {
      if(eq.id() != ID_equal || eq.operands().size() != 2)
        continue;
      // Locate (sym, IF) by checking either side.
      exprt sym, ifexpr;
      if(eq.operands()[1].id() == ID_if)
      {
        sym = eq.operands()[0];
        ifexpr = eq.operands()[1];
      }
      else if(eq.operands()[0].id() == ID_if)
      {
        sym = eq.operands()[1];
        ifexpr = eq.operands()[0];
      }
      else
      {
        continue;
      }
      if(ifexpr.operands().size() != 3)
        continue;
      const exprt &c = ifexpr.operands()[0];
      const exprt &A = ifexpr.operands()[1];
      const exprt &B = ifexpr.operands()[2];
      mp_integer A_val, B_val;
      if(!extract_constant_int(A, A_val) || !extract_constant_int(B, B_val))
        continue;
      if(A_val == B_val)
        continue; // Degenerate; no information.
      if(c.id() != ID_equal || c.operands().size() != 2)
        continue; // Only handle when c is itself an equality.
      // Find a (dis)equality of (sym, constant) matching either branch.
      bool found = false;
      // Disequality case: sym ≠ A ⇒ ¬c; sym ≠ B ⇒ c.
      for(const auto &diseq : algebraic_disequalities)
      {
        if(diseq.id() != ID_equal || diseq.operands().size() != 2)
          continue;
        const exprt &dlhs = diseq.operands()[0];
        const exprt &drhs = diseq.operands()[1];
        mp_integer dconst;
        bool dlhs_const = extract_constant_int(dlhs, dconst);
        bool drhs_const = extract_constant_int(drhs, dconst);
        bool sym_dlhs = exprs_equal(dlhs, sym) && drhs_const;
        bool sym_drhs = exprs_equal(drhs, sym) && dlhs_const;
        if(!sym_dlhs && !sym_drhs)
          continue;
        if(dconst == A_val)
        {
          case_elim_diseqs.push_back(c);
          found = true;
          break;
        }
        else if(dconst == B_val)
        {
          case_elim_eqs.push_back(c);
          found = true;
          break;
        }
      }
      if(found)
        continue;
      // Equality case: sym = A ⇒ c; sym = B ⇒ ¬c. (Mirror of the
      // disequality case.) This handles benchmarks like cohencu_1
      // whose assert 3 is `(not (not (= sym 0)))` ≡ `(= sym 0)`.
      for(const auto &eqq : algebraic_equalities)
      {
        if(&eqq == &eq)
          continue; // Skip the IF-rebuild equality itself.
        if(eqq.id() != ID_equal || eqq.operands().size() != 2)
          continue;
        const exprt &elhs = eqq.operands()[0];
        const exprt &erhs = eqq.operands()[1];
        mp_integer econst;
        bool elhs_const = extract_constant_int(elhs, econst);
        bool erhs_const = extract_constant_int(erhs, econst);
        bool sym_elhs = exprs_equal(elhs, sym) && erhs_const;
        bool sym_erhs = exprs_equal(erhs, sym) && elhs_const;
        if(!sym_elhs && !sym_erhs)
          continue;
        if(econst == A_val)
        {
          case_elim_eqs.push_back(c);
          break;
        }
        else if(econst == B_val)
        {
          case_elim_diseqs.push_back(c);
          break;
        }
      }
    }
    for(auto &e : case_elim_eqs)
      algebraic_equalities.push_back(std::move(e));
    for(auto &e : case_elim_diseqs)
      algebraic_disequalities.push_back(std::move(e));
    if(std::getenv("ALGEBRAIC_WALK_TRACE"))
    {
      std::cerr << "; if-case-elim: +" << case_elim_eqs.size() << " eq, +"
                << case_elim_diseqs.size() << " diseq" << std::endl;
    }
  }

  // Phase 2.6: Tseitin-aware preprocessing. Mine the boolean
  // chains in `algebraic_equalities` for polynomial dis/equalities
  // hidden behind Tseitin-style boolean variables (e.g.,
  // `Fresh__0 ↔ (X = Y)` followed by a chain that fixes Fresh__0
  // to 0 or 1). Adds discovered dis/equalities to the algebraic
  // worklist for the same downstream extraction pipeline. Run
  // BEFORE the empty-disequalities guard so this path can also
  // discover the formula's disequality if it is buried in a
  // Tseitin chain (e.g., wienand commute / distrib benchmarks).
  // Set DISABLE_TSEITIN_PROPAGATION=1 to opt out for ablation.
  // PROOF: formal-proofs/TseitinPropagation.lean (per-rule sound).
  if(std::getenv("DISABLE_TSEITIN_PROPAGATION") == nullptr)
  {
    tseitin_propagatort tseitin_prop;
    tseitin_prop.run(algebraic_equalities);
    if(std::getenv("TSEITIN_TRACE"))
    {
      std::cerr << "; tseitin: " << algebraic_equalities.size()
                << " input equalities, " << tseitin_prop.equalities().size()
                << " new equalities, " << tseitin_prop.disequalities().size()
                << " new disequalities" << std::endl;
      for(const auto &eq : tseitin_prop.equalities())
        std::cerr << "; tseitin eq: " << format(eq) << std::endl;
      for(const auto &eq : tseitin_prop.disequalities())
        std::cerr << "; tseitin diseq: " << format(eq) << std::endl;
    }
    // Only apply tseitin's discoveries when the algebraic solver
    // would otherwise have nothing to refute. This is the case
    // where the polynomial disequality is buried entirely inside
    // a Tseitin chain (e.g., wienand commute / distrib): without
    // tseitin, `algebraic_disequalities` is empty and the early-
    // exit guard below would skip algebraic. With tseitin, we
    // discover the buried disequality. When the algebraic solver
    // is already going to run on other disequalities, adding
    // tseitin's discoveries can cause Buchberger to spend extra
    // work on a SAT instance without changing the verdict; gate
    // it off in that case.
    const bool other_diseqs = !algebraic_disequalities.empty() ||
                              !algebraic_disjunctive_disequalities.empty();
    if(!other_diseqs)
    {
      // Self-contained Tseitin refutation: rather than adding
      // Tseitin's discoveries to `algebraic_*equalities` (which
      // would route through the per-disequality refutation loop
      // below and may trigger the bit-alignment / host-
      // substitution path that, for non-refutable Buchberger
      // runs on bit-mismatched expressions, can fail an
      // invariant on `boolbv_map.cpp::get_literals`), we run a
      // dedicated, simpler Buchberger here. The algebraic state
      // is left untouched on failure.
      //
      // We use a fresh `poly_extractort` and extract polynomials
      // from `algebraic_equalities` best-effort (skipping non-
      // polynomial equalities). For each Tseitin-discovered
      // disequality, build a Rabinowitsch constraint and run
      // plain Buchberger. Skip `materialise_bit_alignments` and
      // host-substitution machinery to avoid the crash path.
      //
      // PROOF: formal-proofs/TseitinPropagation.lean +
      //        formal-proofs/StrongGB.lean::two_trick_unsat_sound.
      // Build SSA substitution map: sym → def for each (= sym X)
      // in algebraic_equalities. Used to expand the disequality's
      // operands fully into the input variables before extraction
      // (the same trick as the inline-products path in the main
      // per-disequality loop, which is what enables the wienand
      // commutativity refutation in the absence of host-
      // substitution / bit-alignment reasoning).
      std::map<irep_idt, exprt> ssa_subst;
      for(const auto &eq : algebraic_equalities)
      {
        if(eq.id() != ID_equal || eq.operands().size() != 2)
          continue;
        const auto &eqe = to_equal_expr(eq);
        if(eqe.lhs().id() == ID_symbol)
          ssa_subst[to_symbol_expr(eqe.lhs()).get_identifier()] = eqe.rhs();
        else if(eqe.rhs().id() == ID_symbol)
          ssa_subst[to_symbol_expr(eqe.rhs()).get_identifier()] = eqe.lhs();
      }
      // Bounded SSA substitution: track current expansion size and
      // abort if it grows beyond `kMaxExpandedNodes`. Also bound
      // the recursion depth to avoid pathological self-loops in
      // SSA chains.
      const std::size_t kMaxExpandedNodes = 50000;
      bool substitution_aborted = false;
      auto count_nodes_local = [](const exprt &e, auto &&self) -> std::size_t
      {
        std::size_t n = 1;
        for(const auto &op : e.operands())
          n += self(op, self);
        return n;
      };
      std::function<void(exprt &, std::size_t)> substitute =
        [&](exprt &e, std::size_t depth)
      {
        if(substitution_aborted)
          return;
        if(depth > 100)
        {
          substitution_aborted = true;
          return;
        }
        for(auto &op : e.operands())
        {
          substitute(op, depth + 1);
          if(substitution_aborted)
            return;
        }
        if(e.id() == ID_symbol)
        {
          auto it = ssa_subst.find(to_symbol_expr(e).get_identifier());
          if(it != ssa_subst.end())
          {
            // Cap on per-substitution expansion: if the
            // replacement is larger than ~200 nodes by itself,
            // don't recurse into it (single-step substitution).
            std::size_t rep_size =
              count_nodes_local(it->second, count_nodes_local);
            if(rep_size > 200)
            {
              e = it->second;
              return; // do not recurse further
            }
            e = it->second;
            substitute(e, depth + 1);
          }
        }
        // Periodic size check: if total size exceeds limit,
        // abort. We can't track the total cheaply, so use a
        // per-node estimate: just stop if we hit a really
        // deep tree.
      };

      auto count_nodes = [&](const exprt &e) -> std::size_t
      { return count_nodes_local(e, count_nodes_local); };

      auto try_refute_one = [&](const equal_exprt &diseq) -> bool
      {
        substitution_aborted = false;
        exprt expanded_diseq = diseq;
        substitute(expanded_diseq, 0);
        if(substitution_aborted)
          return false;
        auto sz = count_nodes(expanded_diseq);
        if(sz > kMaxExpandedNodes)
          return false;
        if(
          expanded_diseq.id() != ID_equal ||
          expanded_diseq.operands().size() != 2)
          return false;

        // Use inline_products to expand bvmul through the
        // substituted expression. This is what makes commutative
        // identities reduce to zero by polynomial canonicalisation.
        poly_extractort inline_extractor;
        inline_extractor.inline_products = true;
        auto ilhs =
          inline_extractor.to_polynomial(to_equal_expr(expanded_diseq).lhs());
        auto irhs =
          inline_extractor.to_polynomial(to_equal_expr(expanded_diseq).rhs());
        if(!ilhs || !irhs)
          return false;
        polynomialt idiff = *ilhs - *irhs;
        idiff.normalize();
        return idiff.is_zero();
      };

      for(const auto &diseq : tseitin_prop.disequalities())
      {
        if(try_refute_one(diseq))
        {
          prop.l_set_to_true(const_literal(false));
          return true;
        }
      }
    }
  }

  if(
    algebraic_disequalities.empty() &&
    algebraic_disjunctive_disequalities.empty())
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

  // Extract universal-relational predicates (Re 4 sub-goal 6) into
  // polynomial constraints. Each predicate may produce multiple
  // polynomials (idempotency for fresh aux bits, recurrence relations,
  // and a final assertion polynomial).
  for(const auto &[pred_expr, pred_val] : algebraic_predicates)
  {
    auto polys = extractor.extract_predicate(pred_expr, pred_val);
    if(!polys.has_value())
      continue;
    for(auto &p : *polys)
    {
      p.normalize();
      if(!p.is_zero())
        equations.push_back(std::move(p));
    }
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
          // Sub-goal 6: feed predicate substitutions (e.g.\ a
          // bvult-induced bit-zeroing constraint) into the inline
          // extractor so the vanishing test can use them. Without
          // this the predicate is invisible to the vanishing path
          // and queries with a relational precondition (e.g.\ the
          // toom-scaled identity) cannot be refuted via vanishing.
          for(const auto &[pred_expr, pred_val] : algebraic_predicates)
            (void)inline_extractor.extract_predicate(pred_expr, pred_val);

          // P2: bit-by-bit parity reasoning. Detect h = c*x patterns
          // (c power of 2) in the inline_extractor's side equations
          // and register the corresponding bit-alignment
          // substitutions. After this the diff of a shift identity
          // collapses under linear elimination.
          (void)inline_extractor.materialise_bit_alignments(
            inline_extractor.side_equations);

          // Apply linear elimination of host variables (Re 4
          // sub-goal 3 follow-on): if idiff contains a host h
          // with sum-decomposition h = sum_i 2^i b_i, substitute
          // h -> sum_i 2^i b_i. After substitution, idiff may
          // collapse to zero (which is trivially vanishing) and
          // we report UNSAT without running the (expensive on
          // bit-decomp variables) vanishing-polynomial test.
          {
            auto host_subs = inline_extractor.get_host_substitutions();
            for(const auto &[host_idx, sub_poly] : host_subs)
              idiff = substitute_variable(idiff, host_idx, sub_poly);
            // Apply Frobenius to keep bit-variable powers in check.
            auto bit_vars = inline_extractor.get_bit_var_indices();
            apply_frobenius_idempotency(idiff, bit_vars);
          }
          if(idiff.is_zero())
          {
            prop.l_set_to_true(const_literal(false));
            return true;
          }
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
    // Universal-relational predicates (Re 4 sub-goal 6).
    for(const auto &[pred_expr, pred_val] : algebraic_predicates)
    {
      auto polys = single_extractor.extract_predicate(pred_expr, pred_val);
      if(!polys.has_value())
        continue;
      for(auto &p : *polys)
      {
        p.normalize();
        if(!p.is_zero())
          single_eqs.push_back(std::move(p));
      }
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

    // Optional: inject ZFP generators for variables.
    // Behind ENABLE_ZFP_INJECTION env var. If on, this is intended
    // to subsume the §3 vanishing polynomial test (set
    // DISABLE_VANISHING=1 to skip the separate test).
    if(std::getenv("ENABLE_ZFP_INJECTION") != nullptr)
    {
      // Optional cap on max k (default = full SF). Keeps the basis
      // small for ablation experiments.
      unsigned max_k_cap = 0;
      unsigned min_k_cap = 2;
      if(const char *cap = std::getenv("ZFP_MAX_K"))
        max_k_cap = std::atoi(cap);
      if(const char *cap = std::getenv("ZFP_MIN_K"))
        min_k_cap = std::atoi(cap);
      const auto &rev_map_d = single_extractor.get_reverse_var_map();
      for(const auto &[var_idx, name] : rev_map_d)
      {
        const std::string name_str = id2string(name);
        if(name_str.substr(0, 2) == "__")
          continue;

        unsigned in_w = single_bw;
        auto it = single_extractor.var_input_widths.find(var_idx);
        if(it != single_extractor.var_input_widths.end() && it->second > 0)
          in_w = it->second;

        auto zfps = generate_zfp_generators(single_bw, var_idx, in_w);
        for(auto &zfp : zfps)
        {
          if(zfp.is_zero())
            continue;
          unsigned deg = zfp.leading_monomial().total_degree();
          if(max_k_cap > 0 && deg > max_k_cap)
            continue;
          if(deg < min_k_cap)
            continue;
          single_eqs.push_back(std::move(zfp));
        }
      }
    }

    if(single_eqs.size() >= 2)
    {
      // P2: bit-by-bit parity reasoning. For each side equation of
      // the form `h - c*x = 0` with c a constant power of 2 and
      // both h, x bit-decomposed, materialise the bit alignments.
      auto alignments = single_extractor.materialise_bit_alignments(single_eqs);
      for(auto &p : alignments)
      {
        if(!p.is_zero())
          single_eqs.push_back(std::move(p));
      }

      strong_groebner_basist single_gb{100000};
      single_gb.set_bit_vars(single_extractor.get_bit_var_indices());
      single_gb.set_host_substitutions(
        single_extractor.get_host_substitutions());
      if(
        single_gb.compute(single_eqs) == strong_groebner_basist::resultt::UNSAT)
      {
        prop.l_set_to_true(const_literal(false));
        return true;
      }
    }
  }

  // Disjunctive disequalities: (or D1 D2 ... Dk) set to true is
  // unsatisfiable iff every Di is unsatisfiable. Reuse the
  // per-disequality machinery: for each Di in the disjunction,
  // run Buchberger with SSA equalities + Rabinowitsch for Di
  // alone. If ALL branches are UNSAT, the disjunction is UNSAT,
  // and so is the whole formula. If any branch is inconclusive,
  // we cannot conclude UNSAT for the disjunction (some other
  // branch might be satisfiable), and we leave the assertion to
  // bit-blasting.
  for(const auto &disjunction : algebraic_disjunctive_disequalities)
  {
    bool all_branches_unsat = true;
    // P4: hoist the SSA substitution map and helper lambda out of
    // the per-branch loop. The map is identical across branches and
    // O(|algebraic_equalities|) to build; computing it once saves
    // O(N * M) total work where N = branches and M = SSA defs.
    std::map<irep_idt, exprt> shared_subst_map;
    for(const auto &eq : algebraic_equalities)
    {
      if(eq.id() == ID_equal)
      {
        const auto &eqe = to_equal_expr(eq);
        if(eqe.lhs().id() == ID_symbol)
          shared_subst_map[to_symbol_expr(eqe.lhs()).get_identifier()] =
            eqe.rhs();
        else if(eqe.rhs().id() == ID_symbol)
          shared_subst_map[to_symbol_expr(eqe.rhs()).get_identifier()] =
            eqe.lhs();
      }
    }

    for(const auto &diseq : disjunction)
    {
      // Per-branch processing mirrors the per-disequality loop above
      // (vanishing-polynomial test + Rabinowitsch + Buchberger).
      poly_extractort branch_extractor;
      auto lhs = branch_extractor.to_polynomial(to_equal_expr(diseq).lhs());
      auto rhs = branch_extractor.to_polynomial(to_equal_expr(diseq).rhs());
      if(!lhs || !rhs)
      {
        all_branches_unsat = false;
        break;
      }
      unsigned branch_bw = branch_extractor.get_bitwidth();
      if(branch_bw == 0)
      {
        all_branches_unsat = false;
        break;
      }
      polynomialt diff = *lhs - *rhs;

      // Vanishing-polynomial test on the diff with SSA-inlined
      // expansion. If the diff is a vanishing polynomial as a
      // function on the bit-vector domain, the disequality is
      // refuted regardless of the rest of the basis. This is the
      // path that decides SABER-style schoolbook-vs-Karatsuba
      // queries: the two implementations produce literally
      // identical polynomials, so the diff polynomial is zero
      // after SSA inlining and the test fires immediately.
      bool branch_refuted_by_vanishing = false;
      {
        std::function<void(exprt &)> substitute = [&](exprt &e)
        {
          for(auto &op : e.operands())
            substitute(op);
          if(e.id() == ID_symbol)
          {
            auto it =
              shared_subst_map.find(to_symbol_expr(e).get_identifier());
            if(it != shared_subst_map.end())
            {
              e = it->second;
              substitute(e);
            }
          }
        };
        exprt expanded = diseq;
        substitute(expanded);
        if(expanded.id() == ID_equal)
        {
          poly_extractort inline_extractor;
          inline_extractor.inline_products = true;
          auto ilhs =
            inline_extractor.to_polynomial(to_equal_expr(expanded).lhs());
          auto irhs =
            inline_extractor.to_polynomial(to_equal_expr(expanded).rhs());
          if(ilhs && irhs)
          {
            polynomialt idiff = *ilhs - *irhs;
            std::vector<unsigned> input_widths(
              inline_extractor.var_input_widths.empty()
                ? 0
                : inline_extractor.var_input_widths.rbegin()->first + 1,
              0);
            for(const auto &[var, w] : inline_extractor.var_input_widths)
              input_widths[var] = w;
            const bool van_disabled =
              std::getenv("DISABLE_VANISHING") != nullptr;
            if(!van_disabled && is_vanishing_polynomial(idiff, input_widths))
              branch_refuted_by_vanishing = true;
          }
        }
      }
      if(branch_refuted_by_vanishing)
        continue; // this branch is UNSAT; try the next branch

      // Fall through to Rabinowitsch + Buchberger.
      std::size_t e_idx = branch_extractor.get_var_index("__rab_disj");
      polynomialt e_var{branch_bw, mp_integer{1}, e_idx};
      polynomialt rab = (diff * e_var) - polynomialt{branch_bw, mp_integer{1}};
      rab.normalize();
      if(rab.is_zero())
      {
        all_branches_unsat = false;
        break;
      }

      std::vector<polynomialt> branch_eqs;
      for(const auto &eq : algebraic_equalities)
      {
        auto poly = branch_extractor.extract_equation(eq);
        if(poly.has_value() && !poly->is_zero())
          branch_eqs.push_back(std::move(*poly));
      }
      // Universal-relational predicates (Re 4 sub-goal 6).
      for(const auto &[pred_expr, pred_val] : algebraic_predicates)
      {
        auto polys = branch_extractor.extract_predicate(pred_expr, pred_val);
        if(!polys.has_value())
          continue;
        for(auto &p : *polys)
        {
          p.normalize();
          if(!p.is_zero())
            branch_eqs.push_back(std::move(p));
        }
      }
      for(auto &se : branch_extractor.side_equations)
      {
        se.normalize();
        if(!se.is_zero())
          branch_eqs.push_back(std::move(se));
      }
      branch_eqs.push_back(std::move(rab));

      if(branch_eqs.size() < 2)
      {
        all_branches_unsat = false;
        break;
      }

      // P2: bit-by-bit parity reasoning.
      auto branch_alignments =
        branch_extractor.materialise_bit_alignments(branch_eqs);
      for(auto &p : branch_alignments)
      {
        if(!p.is_zero())
          branch_eqs.push_back(std::move(p));
      }

      strong_groebner_basist branch_gb{100000};
      branch_gb.set_bit_vars(branch_extractor.get_bit_var_indices());
      branch_gb.set_host_substitutions(
        branch_extractor.get_host_substitutions());
      if(
        branch_gb.compute(branch_eqs) != strong_groebner_basist::resultt::UNSAT)
      {
        all_branches_unsat = false;
        break;
      }
    }
    if(all_branches_unsat)
    {
      // Every branch refuted ⇒ disjunction is UNSAT ⇒ formula is UNSAT.
      prop.l_set_to_true(const_literal(false));
      return true;
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

  // Optional: inject ZFP generators for input-tracked variables.
  // Behind ENABLE_ZFP_INJECTION env var. Set DISABLE_VANISHING=1 in
  // combination if you want to test the hypothesis that ZFP injection
  // subsumes the §3 vanishing polynomial test.
  if(std::getenv("ENABLE_ZFP_INJECTION") != nullptr)
  {
    unsigned bw = extractor.get_bitwidth();
    if(bw > 0)
    {
      unsigned max_k_cap = 0;
      unsigned min_k_cap = 2;
      if(const char *cap = std::getenv("ZFP_MAX_K"))
        max_k_cap = std::atoi(cap);
      if(const char *cap = std::getenv("ZFP_MIN_K"))
        min_k_cap = std::atoi(cap);
      const auto &rev_map = extractor.get_reverse_var_map();
      for(const auto &[var_idx, name] : rev_map)
      {
        // Skip auxiliary variables (Rabinowitsch, fresh product
        // decomposition vars). These are only constrained by the
        // ring's natural ZFPs (which apply automatically); adding
        // ZFP generators for them just bloats the basis.
        const std::string name_str = id2string(name);
        if(name_str.substr(0, 2) == "__")
          continue;

        // Use recorded input width if known (set by zero_extend), else
        // the polynomial ring's bitwidth.
        unsigned in_w = bw;
        auto it = extractor.var_input_widths.find(var_idx);
        if(it != extractor.var_input_widths.end() && it->second > 0)
          in_w = it->second;

        auto zfps = generate_zfp_generators(bw, var_idx, in_w);
        for(auto &zfp : zfps)
        {
          if(zfp.is_zero())
            continue;
          unsigned deg = zfp.leading_monomial().total_degree();
          if(max_k_cap > 0 && deg > max_k_cap)
            continue;
          if(deg < min_k_cap)
            continue;
          equations.push_back(std::move(zfp));
        }
      }
    }
  }

  // P2: bit-by-bit parity reasoning.
  {
    auto alignments = extractor.materialise_bit_alignments(equations);
    for(auto &p : alignments)
    {
      if(!p.is_zero())
        equations.push_back(std::move(p));
    }
  }

  strong_groebner_basist gb{100000};
  gb.set_bit_vars(extractor.get_bit_var_indices());
  gb.set_host_substitutions(extractor.get_host_substitutions());
  auto result = gb.compute(equations);

  if(result == strong_groebner_basist::resultt::UNSAT)
  {
    // Add empty clause to make SAT solver return UNSAT
    prop.l_set_to_true(const_literal(false));
    return true;
  }

  // Item 7 prototype: expression normalisation via the Gröbner basis.
  // After Buchberger, even when the basis didn't decide UNSAT
  // outright, it may now contain enough information to prove
  // individual disequalities false via expression-level reduction.
  // For each disequality (lhs != rhs), reduce its polynomial form
  // (lhs - rhs) w.r.t. the basis. If the reduction yields 0, the
  // basis implies lhs = rhs, contradicting the disequality.
  //
  // This complements the per-disequality Rabinowitsch+Gröbner pass
  // (which runs earlier with each disequality's basis in isolation):
  // the global basis here includes Rabinowitsch polynomials for ALL
  // disequalities simultaneously, so S-polynomials between them can
  // produce reductions no per-disequality pass alone catches.
  //
  // Behind ENABLE_GB_EXPR_NORMALISE for ablation.
  if(std::getenv("ENABLE_GB_EXPR_NORMALISE") != nullptr)
  {
    for(const auto &diseq : algebraic_disequalities)
    {
      if(diseq.id() != ID_equal || diseq.operands().size() != 2)
        continue;
      auto lhs_p = extractor.to_polynomial(to_equal_expr(diseq).lhs());
      auto rhs_p = extractor.to_polynomial(to_equal_expr(diseq).rhs());
      if(!lhs_p || !rhs_p)
        continue;
      polynomialt diff = *lhs_p - *rhs_p;
      diff.normalize();
      if(diff.is_zero())
        continue; // syntactic equality, would be caught by simplifier
      polynomialt reduced =
        strong_groebner_basist::reduce_by_basis(diff, equations, 10000);
      if(reduced.is_zero())
      {
        // The basis implies lhs = rhs, contradicting the disequality.
        prop.l_set_to_true(const_literal(false));
        return true;
      }
    }
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
