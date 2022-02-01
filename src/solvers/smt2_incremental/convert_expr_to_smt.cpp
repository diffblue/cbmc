// Author: Diffblue Ltd.

#include <solvers/smt2_incremental/convert_expr_to_smt.h>

#include <solvers/prop/literal_expr.h>
#include <solvers/smt2_incremental/smt_bit_vector_theory.h>
#include <solvers/smt2_incremental/smt_core_theory.h>
#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/byte_operators.h>
#include <util/expr.h>
#include <util/expr_cast.h>
#include <util/floatbv_expr.h>
#include <util/mathematical_expr.h>
#include <util/pointer_expr.h>
#include <util/pointer_predicates.h>
#include <util/range.h>
#include <util/std_expr.h>
#include <util/string_constant.h>

#include <functional>
#include <numeric>

static smt_sortt convert_type_to_smt_sort(const bool_typet &type)
{
  return smt_bool_sortt{};
}

static smt_sortt convert_type_to_smt_sort(const bitvector_typet &type)
{
  return smt_bit_vector_sortt{type.get_width()};
}

smt_sortt convert_type_to_smt_sort(const typet &type)
{
  if(const auto bool_type = type_try_dynamic_cast<bool_typet>(type))
  {
    return convert_type_to_smt_sort(*bool_type);
  }
  if(const auto bitvector_type = type_try_dynamic_cast<bitvector_typet>(type))
  {
    return convert_type_to_smt_sort(*bitvector_type);
  }
  UNIMPLEMENTED_FEATURE("Generation of SMT formula for type: " + type.pretty());
}

static smt_termt convert_expr_to_smt(const symbol_exprt &symbol_expr)
{
  return smt_identifier_termt{symbol_expr.get_identifier(),
                              convert_type_to_smt_sort(symbol_expr.type())};
}

static smt_termt convert_expr_to_smt(const nondet_symbol_exprt &nondet_symbol)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for nondet symbol expression: " +
    nondet_symbol.pretty());
}

static smt_termt convert_expr_to_smt(const typecast_exprt &cast)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for type cast expression: " + cast.pretty());
}

static smt_termt convert_expr_to_smt(const floatbv_typecast_exprt &float_cast)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for floating point type cast expression: " +
    float_cast.pretty());
}

static smt_termt convert_expr_to_smt(const struct_exprt &struct_construction)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for struct construction expression: " +
    struct_construction.pretty());
}

static smt_termt convert_expr_to_smt(const union_exprt &union_construction)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for union construction expression: " +
    union_construction.pretty());
}

struct sort_based_literal_convertert : public smt_sort_const_downcast_visitort
{
  const constant_exprt &member_input;
  optionalt<smt_termt> result;

  explicit sort_based_literal_convertert(const constant_exprt &input)
    : member_input{input}
  {
  }

  void visit(const smt_bool_sortt &) override
  {
    result = smt_bool_literal_termt{member_input.is_true()};
  }

  void visit(const smt_bit_vector_sortt &bit_vector_sort) override
  {
    const auto &width = bit_vector_sort.bit_width();
    // We get the value using a non-signed interpretation, as smt bit vector
    // terms do not carry signedness.
    const auto value = bvrep2integer(member_input.get_value(), width, false);
    result = smt_bit_vector_constant_termt{value, bit_vector_sort};
  }
};

static smt_termt convert_expr_to_smt(const constant_exprt &constant_literal)
{
  const auto sort = convert_type_to_smt_sort(constant_literal.type());
  sort_based_literal_convertert converter(constant_literal);
  sort.accept(converter);
  return *converter.result;
}

static smt_termt convert_expr_to_smt(const concatenation_exprt &concatenation)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for concatenation expression: " +
    concatenation.pretty());
}

static smt_termt convert_expr_to_smt(const bitand_exprt &bitwise_and_expr)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for bitwise and expression: " +
    bitwise_and_expr.pretty());
}

static smt_termt convert_expr_to_smt(const bitor_exprt &bitwise_or_expr)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for bitwise or expression: " +
    bitwise_or_expr.pretty());
}

static smt_termt convert_expr_to_smt(const bitxor_exprt &bitwise_xor)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for bitwise xor expression: " +
    bitwise_xor.pretty());
}

static smt_termt convert_expr_to_smt(const bitnot_exprt &bitwise_not)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for bitwise not expression: " +
    bitwise_not.pretty());
}

static smt_termt convert_expr_to_smt(const unary_minus_exprt &unary_minus)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for unary minus expression: " +
    unary_minus.pretty());
}

static smt_termt convert_expr_to_smt(const unary_plus_exprt &unary_plus)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for unary plus expression: " +
    unary_plus.pretty());
}

static smt_termt convert_expr_to_smt(const sign_exprt &is_negative)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for \"is negative\" expression: " +
    is_negative.pretty());
}

static smt_termt convert_expr_to_smt(const if_exprt &if_expression)
{
  return smt_core_theoryt::if_then_else(
    convert_expr_to_smt(if_expression.cond()),
    convert_expr_to_smt(if_expression.true_case()),
    convert_expr_to_smt(if_expression.false_case()));
}

/// \brief Converts operator expressions with 2 or more operands to terms
///   expressed as binary operator application.
/// \param expr: The expression to convert.
/// \param factory: The factory function which makes applications of the
///   relevant smt term, when applied to the term operands.
/// \details The conversion used is left associative for instances with 3 or
///   more operands. The SMT standard / core theory version 2.6 actually
///   supports applying the `and`, `or` and `xor` to 3 or more operands.
///   However our internal `smt_core_theoryt` does not support this currently
///   and converting to binary application has the advantage of making the order
///   of evaluation explicit.
template <typename factoryt>
static smt_termt convert_multiary_operator_to_terms(
  const multi_ary_exprt &expr,
  const factoryt &factory)
{
  PRECONDITION(expr.operands().size() >= 2);
  const auto operand_terms =
    make_range(expr.operands()).map([](const exprt &expr) {
      return convert_expr_to_smt(expr);
    });
  return std::accumulate(
    ++operand_terms.begin(),
    operand_terms.end(),
    *operand_terms.begin(),
    factory);
}

static smt_termt convert_expr_to_smt(const and_exprt &and_expression)
{
  return convert_multiary_operator_to_terms(
    and_expression, smt_core_theoryt::make_and);
}

static smt_termt convert_expr_to_smt(const or_exprt &or_expression)
{
  return convert_multiary_operator_to_terms(
    or_expression, smt_core_theoryt::make_or);
}

static smt_termt convert_expr_to_smt(const xor_exprt &xor_expression)
{
  return convert_multiary_operator_to_terms(
    xor_expression, smt_core_theoryt::make_xor);
}

static smt_termt convert_expr_to_smt(const implies_exprt &implies)
{
  return smt_core_theoryt::implies(
    convert_expr_to_smt(implies.op0()), convert_expr_to_smt(implies.op1()));
}

static smt_termt convert_expr_to_smt(const not_exprt &logical_not)
{
  return smt_core_theoryt::make_not(convert_expr_to_smt(logical_not.op()));
}

static smt_termt convert_expr_to_smt(const equal_exprt &equal)
{
  return smt_core_theoryt::equal(
    convert_expr_to_smt(equal.op0()), convert_expr_to_smt(equal.op1()));
}

static smt_termt convert_expr_to_smt(const notequal_exprt &not_equal)
{
  return smt_core_theoryt::distinct(
    convert_expr_to_smt(not_equal.op0()), convert_expr_to_smt(not_equal.op1()));
}

static smt_termt convert_expr_to_smt(const ieee_float_equal_exprt &float_equal)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for floating point equality expression: " +
    float_equal.pretty());
}

static smt_termt
convert_expr_to_smt(const ieee_float_notequal_exprt &float_not_equal)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for floating point not equal expression: " +
    float_not_equal.pretty());
}

template <typename unsigned_factory_typet, typename signed_factory_typet>
static smt_termt convert_relational_to_smt(
  const binary_relation_exprt &binary_relation,
  const unsigned_factory_typet &unsigned_factory,
  const signed_factory_typet &signed_factory)
{
  PRECONDITION(binary_relation.lhs().type() == binary_relation.rhs().type());
  const auto lhs = convert_expr_to_smt(binary_relation.lhs());
  const auto rhs = convert_expr_to_smt(binary_relation.rhs());
  const typet operand_type = binary_relation.lhs().type();
  if(lhs.get_sort().cast<smt_bit_vector_sortt>())
  {
    if(can_cast_type<unsignedbv_typet>(operand_type))
      return unsigned_factory(lhs, rhs);
    if(can_cast_type<signedbv_typet>(operand_type))
      return signed_factory(lhs, rhs);
  }
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for relational expression: " +
    binary_relation.pretty());
}

static optionalt<smt_termt> try_relational_conversion(const exprt &expr)
{
  if(const auto greater_than = expr_try_dynamic_cast<greater_than_exprt>(expr))
  {
    return convert_relational_to_smt(
      *greater_than,
      smt_bit_vector_theoryt::unsigned_greater_than,
      smt_bit_vector_theoryt::signed_greater_than);
  }
  if(
    const auto greater_than_or_equal =
      expr_try_dynamic_cast<greater_than_or_equal_exprt>(expr))
  {
    return convert_relational_to_smt(
      *greater_than_or_equal,
      smt_bit_vector_theoryt::unsigned_greater_than_or_equal,
      smt_bit_vector_theoryt::signed_greater_than_or_equal);
  }
  if(const auto less_than = expr_try_dynamic_cast<less_than_exprt>(expr))
  {
    return convert_relational_to_smt(
      *less_than,
      smt_bit_vector_theoryt::unsigned_less_than,
      smt_bit_vector_theoryt::signed_less_than);
  }
  if(
    const auto less_than_or_equal =
      expr_try_dynamic_cast<less_than_or_equal_exprt>(expr))
  {
    return convert_relational_to_smt(
      *less_than_or_equal,
      smt_bit_vector_theoryt::unsigned_less_than_or_equal,
      smt_bit_vector_theoryt::signed_less_than_or_equal);
  }
  return {};
}

static smt_termt convert_expr_to_smt(const plus_exprt &plus)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for plus expression: " + plus.pretty());
}

static smt_termt convert_expr_to_smt(const minus_exprt &minus)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for minus expression: " + minus.pretty());
}

static smt_termt convert_expr_to_smt(const div_exprt &divide)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for divide expression: " + divide.pretty());
}

static smt_termt convert_expr_to_smt(const ieee_float_op_exprt &float_operation)
{
  // This case includes the floating point plus, minus, division and
  // multiplication operations.
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for floating point operation expression: " +
    float_operation.pretty());
}

static smt_termt convert_expr_to_smt(const mod_exprt &truncation_modulo)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for truncation modulo expression: " +
    truncation_modulo.pretty());
}

static smt_termt
convert_expr_to_smt(const euclidean_mod_exprt &euclidean_modulo)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for euclidean modulo expression: " +
    euclidean_modulo.pretty());
}

static smt_termt convert_expr_to_smt(const mult_exprt &multiply)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for multiply expression: " + multiply.pretty());
}

static smt_termt convert_expr_to_smt(const address_of_exprt &address_of)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for address of expression: " +
    address_of.pretty());
}

static smt_termt convert_expr_to_smt(const array_of_exprt &array_of)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for array of expression: " + array_of.pretty());
}

static smt_termt
convert_expr_to_smt(const array_comprehension_exprt &array_comprehension)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for array comprehension expression: " +
    array_comprehension.pretty());
}

static smt_termt convert_expr_to_smt(const index_exprt &index)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for index expression: " + index.pretty());
}

static smt_termt convert_expr_to_smt(const shift_exprt &shift)
{
  // TODO: split into functions for separate types of shift including rotate.
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for shift expression: " + shift.pretty());
}

static smt_termt convert_expr_to_smt(const with_exprt &with)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for with expression: " + with.pretty());
}

static smt_termt convert_expr_to_smt(const update_exprt &update)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for update expression: " + update.pretty());
}

static smt_termt convert_expr_to_smt(const member_exprt &member_extraction)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for member extraction expression: " +
    member_extraction.pretty());
}

static smt_termt
convert_expr_to_smt(const is_dynamic_object_exprt &is_dynamic_object)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for is dynamic object expression: " +
    is_dynamic_object.pretty());
}

static smt_termt
convert_expr_to_smt(const is_invalid_pointer_exprt &is_invalid_pointer)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for is invalid pointer expression: " +
    is_invalid_pointer.pretty());
}

static smt_termt convert_expr_to_smt(const string_constantt &is_invalid_pointer)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for is invalid pointer expression: " +
    is_invalid_pointer.pretty());
}

static smt_termt convert_expr_to_smt(const extractbit_exprt &extract_bit)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for extract bit expression: " +
    extract_bit.pretty());
}

static smt_termt convert_expr_to_smt(const extractbits_exprt &extract_bits)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for extract bits expression: " +
    extract_bits.pretty());
}

static smt_termt convert_expr_to_smt(const replication_exprt &replication)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for bit vector replication expression: " +
    replication.pretty());
}

static smt_termt convert_expr_to_smt(const byte_extract_exprt &byte_extraction)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for byte extract expression: " +
    byte_extraction.pretty());
}

static smt_termt convert_expr_to_smt(const byte_update_exprt &byte_update)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for byte update expression: " +
    byte_update.pretty());
}

static smt_termt convert_expr_to_smt(const abs_exprt &absolute_value_of)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for absolute value of expression: " +
    absolute_value_of.pretty());
}

static smt_termt convert_expr_to_smt(const isnan_exprt &is_nan_expr)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for is not a number expression: " +
    is_nan_expr.pretty());
}

static smt_termt convert_expr_to_smt(const isfinite_exprt &is_finite_expr)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for is finite expression: " +
    is_finite_expr.pretty());
}

static smt_termt convert_expr_to_smt(const isinf_exprt &is_infinite_expr)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for is infinite expression: " +
    is_infinite_expr.pretty());
}

static smt_termt convert_expr_to_smt(const isnormal_exprt &is_normal_expr)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for is infinite expression: " +
    is_normal_expr.pretty());
}

static smt_termt convert_expr_to_smt(const array_exprt &array_construction)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for array construction expression: " +
    array_construction.pretty());
}

static smt_termt convert_expr_to_smt(const literal_exprt &literal)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for literal expression: " + literal.pretty());
}

static smt_termt convert_expr_to_smt(const forall_exprt &for_all)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for for all expression: " + for_all.pretty());
}

static smt_termt convert_expr_to_smt(const exists_exprt &exists)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for exists expression: " + exists.pretty());
}

static smt_termt convert_expr_to_smt(const vector_exprt &vector)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for vector expression: " + vector.pretty());
}

static smt_termt convert_expr_to_smt(const bswap_exprt &byte_swap)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for byte swap expression: " +
    byte_swap.pretty());
}

static smt_termt convert_expr_to_smt(const popcount_exprt &population_count)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for population count expression: " +
    population_count.pretty());
}

static smt_termt
convert_expr_to_smt(const count_leading_zeros_exprt &count_leading_zeros)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for count leading zeros expression: " +
    count_leading_zeros.pretty());
}

static smt_termt
convert_expr_to_smt(const count_trailing_zeros_exprt &count_trailing_zeros)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for byte swap expression: " +
    count_trailing_zeros.pretty());
}

smt_termt convert_expr_to_smt(const exprt &expr)
{
  if(const auto symbol = expr_try_dynamic_cast<symbol_exprt>(expr))
  {
    return convert_expr_to_smt(*symbol);
  }
  if(const auto nondet = expr_try_dynamic_cast<nondet_symbol_exprt>(expr))
  {
    return convert_expr_to_smt(*nondet);
  }
  if(const auto cast = expr_try_dynamic_cast<typecast_exprt>(expr))
  {
    return convert_expr_to_smt(*cast);
  }
  if(
    const auto float_cast = expr_try_dynamic_cast<floatbv_typecast_exprt>(expr))
  {
    return convert_expr_to_smt(*float_cast);
  }
  if(const auto struct_construction = expr_try_dynamic_cast<struct_exprt>(expr))
  {
    return convert_expr_to_smt(*struct_construction);
  }
  if(const auto union_construction = expr_try_dynamic_cast<union_exprt>(expr))
  {
    return convert_expr_to_smt(*union_construction);
  }
  if(const auto constant_literal = expr_try_dynamic_cast<constant_exprt>(expr))
  {
    return convert_expr_to_smt(*constant_literal);
  }
  if(
    const auto concatenation = expr_try_dynamic_cast<concatenation_exprt>(expr))
  {
    return convert_expr_to_smt(*concatenation);
  }
  if(const auto bitwise_and_expr = expr_try_dynamic_cast<bitand_exprt>(expr))
  {
    return convert_expr_to_smt(*bitwise_and_expr);
  }
  if(const auto bitwise_or_expr = expr_try_dynamic_cast<bitor_exprt>(expr))
  {
    return convert_expr_to_smt(*bitwise_or_expr);
  }
  if(const auto bitwise_xor = expr_try_dynamic_cast<bitxor_exprt>(expr))
  {
    return convert_expr_to_smt(*bitwise_xor);
  }
  if(const auto bitwise_not = expr_try_dynamic_cast<bitnot_exprt>(expr))
  {
    return convert_expr_to_smt(*bitwise_not);
  }
  if(const auto unary_minus = expr_try_dynamic_cast<unary_minus_exprt>(expr))
  {
    return convert_expr_to_smt(*unary_minus);
  }
  if(const auto unary_plus = expr_try_dynamic_cast<unary_plus_exprt>(expr))
  {
    return convert_expr_to_smt(*unary_plus);
  }
  if(const auto is_negative = expr_try_dynamic_cast<sign_exprt>(expr))
  {
    return convert_expr_to_smt(*is_negative);
  }
  if(const auto if_expression = expr_try_dynamic_cast<if_exprt>(expr))
  {
    return convert_expr_to_smt(*if_expression);
  }
  if(const auto and_expression = expr_try_dynamic_cast<and_exprt>(expr))
  {
    return convert_expr_to_smt(*and_expression);
  }
  if(const auto or_expression = expr_try_dynamic_cast<or_exprt>(expr))
  {
    return convert_expr_to_smt(*or_expression);
  }
  if(const auto xor_expression = expr_try_dynamic_cast<xor_exprt>(expr))
  {
    return convert_expr_to_smt(*xor_expression);
  }
  if(const auto implies = expr_try_dynamic_cast<implies_exprt>(expr))
  {
    return convert_expr_to_smt(*implies);
  }
  if(const auto logical_not = expr_try_dynamic_cast<not_exprt>(expr))
  {
    return convert_expr_to_smt(*logical_not);
  }
  if(const auto equal = expr_try_dynamic_cast<equal_exprt>(expr))
  {
    return convert_expr_to_smt(*equal);
  }
  if(const auto not_equal = expr_try_dynamic_cast<notequal_exprt>(expr))
  {
    return convert_expr_to_smt(*not_equal);
  }
  if(
    const auto float_equal =
      expr_try_dynamic_cast<ieee_float_equal_exprt>(expr))
  {
    return convert_expr_to_smt(*float_equal);
  }
  if(
    const auto float_not_equal =
      expr_try_dynamic_cast<ieee_float_notequal_exprt>(expr))
  {
    return convert_expr_to_smt(*float_not_equal);
  }
  if(const auto converted_relational = try_relational_conversion(expr))
  {
    return *converted_relational;
  }
  if(const auto plus = expr_try_dynamic_cast<plus_exprt>(expr))
  {
    return convert_expr_to_smt(*plus);
  }
  if(const auto minus = expr_try_dynamic_cast<minus_exprt>(expr))
  {
    return convert_expr_to_smt(*minus);
  }
  if(const auto divide = expr_try_dynamic_cast<div_exprt>(expr))
  {
    return convert_expr_to_smt(*divide);
  }
  if(
    const auto float_operation =
      expr_try_dynamic_cast<ieee_float_op_exprt>(expr))
  {
    return convert_expr_to_smt(*float_operation);
  }
  if(const auto truncation_modulo = expr_try_dynamic_cast<mod_exprt>(expr))
  {
    return convert_expr_to_smt(*truncation_modulo);
  }
  if(
    const auto euclidean_modulo =
      expr_try_dynamic_cast<euclidean_mod_exprt>(expr))
  {
    return convert_expr_to_smt(*euclidean_modulo);
  }
  if(const auto multiply = expr_try_dynamic_cast<mult_exprt>(expr))
  {
    return convert_expr_to_smt(*multiply);
  }
#if 0
  else if(expr.id() == ID_floatbv_rem)
  {
    convert_floatbv_rem(to_binary_expr(expr));
  }
#endif
  if(const auto address_of = expr_try_dynamic_cast<address_of_exprt>(expr))
  {
    return convert_expr_to_smt(*address_of);
  }
  if(const auto array_of = expr_try_dynamic_cast<array_of_exprt>(expr))
  {
    return convert_expr_to_smt(*array_of);
  }
  if(
    const auto array_comprehension =
      expr_try_dynamic_cast<array_comprehension_exprt>(expr))
  {
    return convert_expr_to_smt(*array_comprehension);
  }
  if(const auto index = expr_try_dynamic_cast<index_exprt>(expr))
  {
    return convert_expr_to_smt(*index);
  }
  if(const auto shift = expr_try_dynamic_cast<shift_exprt>(expr))
  {
    return convert_expr_to_smt(*shift);
  }
  if(const auto with = expr_try_dynamic_cast<with_exprt>(expr))
  {
    return convert_expr_to_smt(*with);
  }
  if(const auto update = expr_try_dynamic_cast<update_exprt>(expr))
  {
    return convert_expr_to_smt(*update);
  }
  if(const auto member_extraction = expr_try_dynamic_cast<member_exprt>(expr))
  {
    return convert_expr_to_smt(*member_extraction);
  }
#if 0
  else if(expr.id()==ID_pointer_offset)
  {
  }
  else if(expr.id()==ID_pointer_object)
  {
  }
#endif
  if(
    const auto is_dynamic_object =
      expr_try_dynamic_cast<is_dynamic_object_exprt>(expr))
  {
    return convert_expr_to_smt(*is_dynamic_object);
  }
  if(
    const auto is_invalid_pointer =
      expr_try_dynamic_cast<is_invalid_pointer_exprt>(expr))
  {
    return convert_expr_to_smt(*is_invalid_pointer);
  }
  if(const auto string_constant = expr_try_dynamic_cast<string_constantt>(expr))
  {
    return convert_expr_to_smt(*string_constant);
  }
  if(const auto extract_bit = expr_try_dynamic_cast<extractbit_exprt>(expr))
  {
    return convert_expr_to_smt(*extract_bit);
  }
  if(const auto extract_bits = expr_try_dynamic_cast<extractbits_exprt>(expr))
  {
    return convert_expr_to_smt(*extract_bits);
  }
  if(const auto replication = expr_try_dynamic_cast<replication_exprt>(expr))
  {
    return convert_expr_to_smt(*replication);
  }
  if(
    const auto byte_extraction =
      expr_try_dynamic_cast<byte_extract_exprt>(expr))
  {
    return convert_expr_to_smt(*byte_extraction);
  }
  if(const auto byte_update = expr_try_dynamic_cast<byte_update_exprt>(expr))
  {
    return convert_expr_to_smt(*byte_update);
  }
  if(const auto absolute_value_of = expr_try_dynamic_cast<abs_exprt>(expr))
  {
    return convert_expr_to_smt(*absolute_value_of);
  }
  if(const auto is_nan_expr = expr_try_dynamic_cast<isnan_exprt>(expr))
  {
    return convert_expr_to_smt(*is_nan_expr);
  }
  if(const auto is_finite_expr = expr_try_dynamic_cast<isfinite_exprt>(expr))
  {
    return convert_expr_to_smt(*is_finite_expr);
  }
  if(const auto is_infinite_expr = expr_try_dynamic_cast<isinf_exprt>(expr))
  {
    return convert_expr_to_smt(*is_infinite_expr);
  }
  if(const auto is_normal_expr = expr_try_dynamic_cast<isnormal_exprt>(expr))
  {
    return convert_expr_to_smt(*is_normal_expr);
  }
  if(const auto array_construction = expr_try_dynamic_cast<array_exprt>(expr))
  {
    return convert_expr_to_smt(*array_construction);
  }
  if(const auto literal = expr_try_dynamic_cast<literal_exprt>(expr))
  {
    return convert_expr_to_smt(*literal);
  }
  if(const auto for_all = expr_try_dynamic_cast<forall_exprt>(expr))
  {
    return convert_expr_to_smt(*for_all);
  }
  if(const auto exists = expr_try_dynamic_cast<exists_exprt>(expr))
  {
    return convert_expr_to_smt(*exists);
  }
  if(const auto vector = expr_try_dynamic_cast<vector_exprt>(expr))
  {
    return convert_expr_to_smt(*vector);
  }
#if 0
  else if(expr.id()==ID_object_size)
  {
    out << "|" << object_sizes[expr] << "|";
  }
#endif
  if(const auto let = expr_try_dynamic_cast<let_exprt>(expr))
  {
    return convert_expr_to_smt(*let);
  }
  INVARIANT(
    expr.id() != ID_constraint_select_one,
    "constraint_select_one is not expected in smt conversion: " +
      expr.pretty());
  if(const auto byte_swap = expr_try_dynamic_cast<bswap_exprt>(expr))
  {
    return convert_expr_to_smt(*byte_swap);
  }
  if(const auto population_count = expr_try_dynamic_cast<popcount_exprt>(expr))
  {
    return convert_expr_to_smt(*population_count);
  }
  if(
    const auto count_leading_zeros =
      expr_try_dynamic_cast<count_leading_zeros_exprt>(expr))
  {
    return convert_expr_to_smt(*count_leading_zeros);
  }
  if(
    const auto count_trailing_zeros =
      expr_try_dynamic_cast<count_trailing_zeros_exprt>(expr))
  {
    return convert_expr_to_smt(*count_trailing_zeros);
  }

  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for unknown kind of expression: " +
    expr.pretty());
}
