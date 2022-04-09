// Author: Diffblue Ltd.

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/expr.h>
#include <util/expr_cast.h>
#include <util/expr_util.h>
#include <util/floatbv_expr.h>
#include <util/mathematical_expr.h>
#include <util/pointer_expr.h>
#include <util/pointer_predicates.h>
#include <util/range.h>
#include <util/std_expr.h>
#include <util/string_constant.h>

#include <solvers/prop/literal_expr.h>
#include <solvers/smt2_incremental/convert_expr_to_smt.h>
#include <solvers/smt2_incremental/smt_bit_vector_theory.h>
#include <solvers/smt2_incremental/smt_core_theory.h>

#include <functional>
#include <numeric>

/// Post order visitation is used in order to construct the the smt terms bottom
/// upwards without using recursion to traverse the input `exprt`. Therefore
/// the `convert_expr_to_smt` overload for any given type of `exprt`, will
/// be passed a sub_expression_map which already contains the result of
/// converting that expressions operands to smt terms. This has the advantages
/// of -
///   * avoiding the deeply nested call stacks associated with recursion.
///   * supporting wider scope for the conversion of specific types of `exprt`,
///     without inflating the parameter list / scope for all conversions.
using sub_expression_mapt =
  std::unordered_map<exprt, smt_termt, irep_full_hash>;

/// \brief Converts operator expressions with 2 or more operands to terms
///   expressed as binary operator application.
/// \param expr: The expression to convert.
/// \param converted: Map for looking up previously converted sub expressions.
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
  const sub_expression_mapt &converted,
  const factoryt &factory)
{
  PRECONDITION(expr.operands().size() >= 2);
  const auto operand_terms =
    make_range(expr.operands()).map([&](const exprt &expr) {
      return converted.at(expr);
    });
  return std::accumulate(
    ++operand_terms.begin(),
    operand_terms.end(),
    *operand_terms.begin(),
    factory);
}

/// \brief Ensures that all operands of the argument expression have related
///   types.
/// \param expr: The expression of which the operands we evaluate for type
///   equality.
template <typename target_typet>
static bool operands_are_of_type(const exprt &expr)
{
  return std::all_of(
    expr.operands().cbegin(), expr.operands().cend(), [](const exprt &operand) {
      return can_cast_type<target_typet>(operand.type());
    });
}

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

static smt_termt convert_expr_to_smt(
  const nondet_symbol_exprt &nondet_symbol,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for nondet symbol expression: " +
    nondet_symbol.pretty());
}

/// \brief Makes a term which is true if \p input is not 0 / false.
static smt_termt make_not_zero(const smt_termt &input, const typet &source_type)
{
  if(input.get_sort().cast<smt_bool_sortt>())
    return input;
  if(const auto bit_vector_sort = input.get_sort().cast<smt_bit_vector_sortt>())
  {
    return smt_core_theoryt::distinct(
      input, smt_bit_vector_constant_termt{0, *bit_vector_sort});
  }
  UNREACHABLE;
}

/// \brief Returns a cast to C bool expressed in smt terms.
static smt_termt convert_c_bool_cast(
  const smt_termt &from_term,
  const typet &from_type,
  const bitvector_typet &to_type)
{
  const std::size_t c_bool_width = to_type.get_width();
  return smt_core_theoryt::if_then_else(
    make_not_zero(from_term, from_type),
    smt_bit_vector_constant_termt{1, c_bool_width},
    smt_bit_vector_constant_termt{0, c_bool_width});
}

static std::function<std::function<smt_termt(smt_termt)>(std::size_t)>
extension_for_type(const typet &type)
{
  if(can_cast_type<signedbv_typet>(type))
    return smt_bit_vector_theoryt::sign_extend;
  if(can_cast_type<unsignedbv_typet>(type))
    return smt_bit_vector_theoryt::zero_extend;
  UNREACHABLE;
}

static smt_termt make_bitvector_resize_cast(
  const smt_termt &from_term,
  const bitvector_typet &from_type,
  const bitvector_typet &to_type)
{
  if(const auto to_fixedbv_type = type_try_dynamic_cast<fixedbv_typet>(to_type))
  {
    UNIMPLEMENTED_FEATURE(
      "Generation of SMT formula for type cast to fixed-point bitvector "
      "type: " +
      to_type.pretty());
  }
  if(const auto to_floatbv_type = type_try_dynamic_cast<floatbv_typet>(to_type))
  {
    UNIMPLEMENTED_FEATURE(
      "Generation of SMT formula for type cast to floating-point bitvector "
      "type: " +
      to_type.pretty());
  }
  const std::size_t from_width = from_type.get_width();
  const std::size_t to_width = to_type.get_width();
  if(to_width == from_width)
    return from_term;
  if(to_width < from_width)
    return smt_bit_vector_theoryt::extract(to_width - 1, 0)(from_term);
  const std::size_t extension_size = to_width - from_width;
  return extension_for_type(from_type)(extension_size)(from_term);
}

struct sort_based_cast_to_bit_vector_convertert final
  : public smt_sort_const_downcast_visitort
{
  const smt_termt &from_term;
  const typet &from_type;
  const bitvector_typet &to_type;
  optionalt<smt_termt> result;

  sort_based_cast_to_bit_vector_convertert(
    const smt_termt &from_term,
    const typet &from_type,
    const bitvector_typet &to_type)
    : from_term{from_term}, from_type{from_type}, to_type{to_type}
  {
  }

  void visit(const smt_bool_sortt &) override
  {
    result = convert_c_bool_cast(
      from_term, from_type, c_bool_typet{to_type.get_width()});
  }

  void visit(const smt_bit_vector_sortt &) override
  {
    if(const auto bitvector = type_try_dynamic_cast<bitvector_typet>(from_type))
      result = make_bitvector_resize_cast(from_term, *bitvector, to_type);
    else
      UNIMPLEMENTED_FEATURE(
        "Generation of SMT formula for type cast to bit vector from type: " +
        from_type.pretty());
  }
};

static smt_termt convert_bit_vector_cast(
  const smt_termt &from_term,
  const typet &from_type,
  const bitvector_typet &to_type)
{
  sort_based_cast_to_bit_vector_convertert converter{
    from_term, from_type, to_type};
  from_term.get_sort().accept(converter);
  POSTCONDITION(converter.result);
  return *converter.result;
}

static smt_termt convert_expr_to_smt(
  const typecast_exprt &cast,
  const sub_expression_mapt &converted)
{
  const auto &from_term = converted.at(cast.op());
  const typet &from_type = cast.op().type();
  const typet &to_type = cast.type();
  if(const auto bool_type = type_try_dynamic_cast<bool_typet>(to_type))
    return make_not_zero(from_term, cast.op().type());
  if(const auto c_bool_type = type_try_dynamic_cast<c_bool_typet>(to_type))
    return convert_c_bool_cast(from_term, from_type, *c_bool_type);
  if(const auto bit_vector = type_try_dynamic_cast<bitvector_typet>(to_type))
    return convert_bit_vector_cast(from_term, from_type, *bit_vector);
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for type cast expression: " + cast.pretty());
}

static smt_termt convert_expr_to_smt(
  const floatbv_typecast_exprt &float_cast,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for floating point type cast expression: " +
    float_cast.pretty());
}

static smt_termt convert_expr_to_smt(
  const struct_exprt &struct_construction,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for struct construction expression: " +
    struct_construction.pretty());
}

static smt_termt convert_expr_to_smt(
  const union_exprt &union_construction,
  const sub_expression_mapt &converted)
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
  if(is_null_pointer(constant_literal))
  {
    const size_t bit_width =
      type_checked_cast<pointer_typet>(constant_literal.type()).get_width();
    // An address of 0 encodes an object identifier of 0 for the NULL object
    // and an offset of 0 into the object.
    const auto address = 0;
    return smt_bit_vector_constant_termt{address, bit_width};
  }
  if(constant_literal.type() == integer_typet{})
  {
    // This is converting integer constants into bit vectors for use with
    // bit vector based smt logics. As bit vector widths are not specified for
    // non bit vector types, this chooses a width based on the minimum needed
    // to hold the integer constant value.
    const auto value = numeric_cast_v<mp_integer>(constant_literal);
    return smt_bit_vector_constant_termt{value, address_bits(value + 1)};
  }
  const auto sort = convert_type_to_smt_sort(constant_literal.type());
  sort_based_literal_convertert converter(constant_literal);
  sort.accept(converter);
  return *converter.result;
}

static smt_termt convert_expr_to_smt(
  const concatenation_exprt &concatenation,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for concatenation expression: " +
    concatenation.pretty());
}

static smt_termt convert_expr_to_smt(
  const bitand_exprt &bitwise_and_expr,
  const sub_expression_mapt &converted)
{
  if(operands_are_of_type<integer_bitvector_typet>(bitwise_and_expr))
  {
    return convert_multiary_operator_to_terms(
      bitwise_and_expr, converted, smt_bit_vector_theoryt::make_and);
  }
  else
  {
    UNIMPLEMENTED_FEATURE(
      "Generation of SMT formula for bitwise and expression: " +
      bitwise_and_expr.pretty());
  }
}

static smt_termt convert_expr_to_smt(
  const bitor_exprt &bitwise_or_expr,
  const sub_expression_mapt &converted)
{
  if(operands_are_of_type<integer_bitvector_typet>(bitwise_or_expr))
  {
    return convert_multiary_operator_to_terms(
      bitwise_or_expr, converted, smt_bit_vector_theoryt::make_or);
  }
  else
  {
    UNIMPLEMENTED_FEATURE(
      "Generation of SMT formula for bitwise or expression: " +
      bitwise_or_expr.pretty());
  }
}

static smt_termt convert_expr_to_smt(
  const bitxor_exprt &bitwise_xor,
  const sub_expression_mapt &converted)
{
  if(operands_are_of_type<integer_bitvector_typet>(bitwise_xor))
  {
    return convert_multiary_operator_to_terms(
      bitwise_xor, converted, smt_bit_vector_theoryt::make_xor);
  }
  else
  {
    UNIMPLEMENTED_FEATURE(
      "Generation of SMT formula for bitwise xor expression: " +
      bitwise_xor.pretty());
  }
}

static smt_termt convert_expr_to_smt(
  const bitnot_exprt &bitwise_not,
  const sub_expression_mapt &converted)
{
  const bool operand_is_bitvector =
    can_cast_type<integer_bitvector_typet>(bitwise_not.op().type());

  if(operand_is_bitvector)
  {
    return smt_bit_vector_theoryt::make_not(converted.at(bitwise_not.op()));
  }
  else
  {
    UNIMPLEMENTED_FEATURE(
      "Generation of SMT formula for bitnot_exprt: " + bitwise_not.pretty());
  }
}

static smt_termt convert_expr_to_smt(
  const unary_minus_exprt &unary_minus,
  const sub_expression_mapt &converted)
{
  const bool operand_is_bitvector =
    can_cast_type<integer_bitvector_typet>(unary_minus.op().type());
  if(operand_is_bitvector)
  {
    return smt_bit_vector_theoryt::negate(converted.at(unary_minus.op()));
  }
  else
  {
    UNIMPLEMENTED_FEATURE(
      "Generation of SMT formula for unary minus expression: " +
      unary_minus.pretty());
  }
}

static smt_termt convert_expr_to_smt(
  const unary_plus_exprt &unary_plus,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for unary plus expression: " +
    unary_plus.pretty());
}

static smt_termt convert_expr_to_smt(
  const sign_exprt &is_negative,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for \"is negative\" expression: " +
    is_negative.pretty());
}

static smt_termt convert_expr_to_smt(
  const if_exprt &if_expression,
  const sub_expression_mapt &converted)
{
  return smt_core_theoryt::if_then_else(
    converted.at(if_expression.cond()),
    converted.at(if_expression.true_case()),
    converted.at(if_expression.false_case()));
}

static smt_termt convert_expr_to_smt(
  const and_exprt &and_expression,
  const sub_expression_mapt &converted)
{
  return convert_multiary_operator_to_terms(
    and_expression, converted, smt_core_theoryt::make_and);
}

static smt_termt convert_expr_to_smt(
  const or_exprt &or_expression,
  const sub_expression_mapt &converted)
{
  return convert_multiary_operator_to_terms(
    or_expression, converted, smt_core_theoryt::make_or);
}

static smt_termt convert_expr_to_smt(
  const xor_exprt &xor_expression,
  const sub_expression_mapt &converted)
{
  return convert_multiary_operator_to_terms(
    xor_expression, converted, smt_core_theoryt::make_xor);
}

static smt_termt convert_expr_to_smt(
  const implies_exprt &implies,
  const sub_expression_mapt &converted)
{
  return smt_core_theoryt::implies(
    converted.at(implies.op0()), converted.at(implies.op1()));
}

static smt_termt convert_expr_to_smt(
  const not_exprt &logical_not,
  const sub_expression_mapt &converted)
{
  return smt_core_theoryt::make_not(converted.at(logical_not.op()));
}

static smt_termt convert_expr_to_smt(
  const equal_exprt &equal,
  const sub_expression_mapt &converted)
{
  return smt_core_theoryt::equal(
    converted.at(equal.op0()), converted.at(equal.op1()));
}

static smt_termt convert_expr_to_smt(
  const notequal_exprt &not_equal,
  const sub_expression_mapt &converted)
{
  return smt_core_theoryt::distinct(
    converted.at(not_equal.op0()), converted.at(not_equal.op1()));
}

static smt_termt convert_expr_to_smt(
  const ieee_float_equal_exprt &float_equal,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for floating point equality expression: " +
    float_equal.pretty());
}

static smt_termt convert_expr_to_smt(
  const ieee_float_notequal_exprt &float_not_equal,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for floating point not equal expression: " +
    float_not_equal.pretty());
}

template <typename unsigned_factory_typet, typename signed_factory_typet>
static smt_termt convert_relational_to_smt(
  const binary_relation_exprt &binary_relation,
  const unsigned_factory_typet &unsigned_factory,
  const signed_factory_typet &signed_factory,
  const sub_expression_mapt &converted)
{
  PRECONDITION(binary_relation.lhs().type() == binary_relation.rhs().type());
  const auto &lhs = converted.at(binary_relation.lhs());
  const auto &rhs = converted.at(binary_relation.rhs());
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

static optionalt<smt_termt> try_relational_conversion(
  const exprt &expr,
  const sub_expression_mapt &converted)
{
  if(const auto greater_than = expr_try_dynamic_cast<greater_than_exprt>(expr))
  {
    return convert_relational_to_smt(
      *greater_than,
      smt_bit_vector_theoryt::unsigned_greater_than,
      smt_bit_vector_theoryt::signed_greater_than,
      converted);
  }
  if(
    const auto greater_than_or_equal =
      expr_try_dynamic_cast<greater_than_or_equal_exprt>(expr))
  {
    return convert_relational_to_smt(
      *greater_than_or_equal,
      smt_bit_vector_theoryt::unsigned_greater_than_or_equal,
      smt_bit_vector_theoryt::signed_greater_than_or_equal,
      converted);
  }
  if(const auto less_than = expr_try_dynamic_cast<less_than_exprt>(expr))
  {
    return convert_relational_to_smt(
      *less_than,
      smt_bit_vector_theoryt::unsigned_less_than,
      smt_bit_vector_theoryt::signed_less_than,
      converted);
  }
  if(
    const auto less_than_or_equal =
      expr_try_dynamic_cast<less_than_or_equal_exprt>(expr))
  {
    return convert_relational_to_smt(
      *less_than_or_equal,
      smt_bit_vector_theoryt::unsigned_less_than_or_equal,
      smt_bit_vector_theoryt::signed_less_than_or_equal,
      converted);
  }
  return {};
}

static smt_termt convert_expr_to_smt(
  const plus_exprt &plus,
  const sub_expression_mapt &converted)
{
  if(std::all_of(
       plus.operands().cbegin(), plus.operands().cend(), [](exprt operand) {
         return can_cast_type<integer_bitvector_typet>(operand.type());
       }))
  {
    return convert_multiary_operator_to_terms(
      plus, converted, smt_bit_vector_theoryt::add);
  }
  else
  {
    UNIMPLEMENTED_FEATURE(
      "Generation of SMT formula for plus expression: " + plus.pretty());
  }
}

static smt_termt convert_expr_to_smt(
  const minus_exprt &minus,
  const sub_expression_mapt &converted)
{
  const bool both_operands_bitvector =
    can_cast_type<integer_bitvector_typet>(minus.lhs().type()) &&
    can_cast_type<integer_bitvector_typet>(minus.rhs().type());

  if(both_operands_bitvector)
  {
    return smt_bit_vector_theoryt::subtract(
      converted.at(minus.lhs()), converted.at(minus.rhs()));
  }
  else
  {
    UNIMPLEMENTED_FEATURE(
      "Generation of SMT formula for minus expression: " + minus.pretty());
  }
}

static smt_termt convert_expr_to_smt(
  const div_exprt &divide,
  const sub_expression_mapt &converted)
{
  const smt_termt &lhs = converted.at(divide.lhs());
  const smt_termt &rhs = converted.at(divide.rhs());

  const bool both_operands_bitvector =
    can_cast_type<integer_bitvector_typet>(divide.lhs().type()) &&
    can_cast_type<integer_bitvector_typet>(divide.rhs().type());

  const bool both_operands_unsigned =
    can_cast_type<unsignedbv_typet>(divide.lhs().type()) &&
    can_cast_type<unsignedbv_typet>(divide.rhs().type());

  if(both_operands_bitvector)
  {
    if(both_operands_unsigned)
    {
      return smt_bit_vector_theoryt::unsigned_divide(lhs, rhs);
    }
    else
    {
      return smt_bit_vector_theoryt::signed_divide(lhs, rhs);
    }
  }
  else
  {
    UNIMPLEMENTED_FEATURE(
      "Generation of SMT formula for divide expression: " + divide.pretty());
  }
}

static smt_termt convert_expr_to_smt(
  const ieee_float_op_exprt &float_operation,
  const sub_expression_mapt &converted)
{
  // This case includes the floating point plus, minus, division and
  // multiplication operations.
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for floating point operation expression: " +
    float_operation.pretty());
}

static smt_termt convert_expr_to_smt(
  const mod_exprt &truncation_modulo,
  const sub_expression_mapt &converted)
{
  const smt_termt &lhs = converted.at(truncation_modulo.lhs());
  const smt_termt &rhs = converted.at(truncation_modulo.rhs());

  const bool both_operands_bitvector =
    can_cast_type<integer_bitvector_typet>(truncation_modulo.lhs().type()) &&
    can_cast_type<integer_bitvector_typet>(truncation_modulo.rhs().type());

  const bool both_operands_unsigned =
    can_cast_type<unsignedbv_typet>(truncation_modulo.lhs().type()) &&
    can_cast_type<unsignedbv_typet>(truncation_modulo.rhs().type());

  if(both_operands_bitvector)
  {
    if(both_operands_unsigned)
    {
      return smt_bit_vector_theoryt::unsigned_remainder(lhs, rhs);
    }
    else
    {
      return smt_bit_vector_theoryt::signed_remainder(lhs, rhs);
    }
  }
  else
  {
    UNIMPLEMENTED_FEATURE(
      "Generation of SMT formula for remainder (modulus) expression: " +
      truncation_modulo.pretty());
  }
}

static smt_termt convert_expr_to_smt(
  const euclidean_mod_exprt &euclidean_modulo,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for euclidean modulo expression: " +
    euclidean_modulo.pretty());
}

static smt_termt convert_expr_to_smt(
  const mult_exprt &multiply,
  const sub_expression_mapt &converted)
{
  if(std::all_of(
       multiply.operands().cbegin(),
       multiply.operands().cend(),
       [](exprt operand) {
         return can_cast_type<integer_bitvector_typet>(operand.type());
       }))
  {
    return convert_multiary_operator_to_terms(
      multiply, converted, smt_bit_vector_theoryt::multiply);
  }
  else
  {
    UNIMPLEMENTED_FEATURE(
      "Generation of SMT formula for multiply expression: " +
      multiply.pretty());
  }
}

#ifndef CPROVER_INVARIANT_DO_NOT_CHECK
static mp_integer power2(unsigned exponent)
{
  mp_integer result;
  result.setPower2(exponent);
  return result;
}
#endif

/// \details
/// This conversion constructs a bit vector representation of the memory
/// address. This address is composed of 2 concatenated bit vector components.
/// The first part is the base object's unique identifier. The second is the
/// offset into that object. For address of symbols the offset will be 0. The
/// offset may be non-zero for cases such as the address of a member field of a
/// struct or a the address of a non-zero index into an array.
static smt_termt convert_expr_to_smt(
  const address_of_exprt &address_of,
  const sub_expression_mapt &converted,
  const smt_object_mapt &object_map)
{
  const auto type = type_try_dynamic_cast<pointer_typet>(address_of.type());
  INVARIANT(
    type, "Result of the address_of operator should have pointer type.");
  const auto base = find_object_base_expression(address_of);
  const auto object = object_map.find(base);
  INVARIANT(
    object != object_map.end(),
    "Objects should be tracked before converting their address to SMT terms");
  const std::size_t object_id = object->second.unique_id;
  INVARIANT(
    object_id < power2(config.bv_encoding.object_bits),
    "There should be sufficient bits to encode unique object identifier.");
  const smt_termt object_bit_vector =
    smt_bit_vector_constant_termt{object_id, config.bv_encoding.object_bits};
  INVARIANT(
    type->get_width() > config.bv_encoding.object_bits,
    "Pointer should be wider than object_bits in order to allow for offset "
    "encoding.");
  const size_t offset_bits = type->get_width() - config.bv_encoding.object_bits;
  if(
    const auto symbol =
      expr_try_dynamic_cast<symbol_exprt>(address_of.object()))
  {
    const smt_bit_vector_constant_termt offset{0, offset_bits};
    return smt_bit_vector_theoryt::concat(object_bit_vector, offset);
  }
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for address of expression: " +
    address_of.pretty());
}

static smt_termt convert_expr_to_smt(
  const array_of_exprt &array_of,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for array of expression: " + array_of.pretty());
}

static smt_termt convert_expr_to_smt(
  const array_comprehension_exprt &array_comprehension,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for array comprehension expression: " +
    array_comprehension.pretty());
}

static smt_termt convert_expr_to_smt(
  const index_exprt &index,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for index expression: " + index.pretty());
}

template <typename factoryt, typename shiftt>
static smt_termt convert_to_smt_shift(
  const factoryt &factory,
  const shiftt &shift,
  const sub_expression_mapt &converted)
{
  const smt_termt &first_operand = converted.at(shift.op0());
  const smt_termt &second_operand = converted.at(shift.op1());
  const auto first_bit_vector_sort =
    first_operand.get_sort().cast<smt_bit_vector_sortt>();
  const auto second_bit_vector_sort =
    second_operand.get_sort().cast<smt_bit_vector_sortt>();
  INVARIANT(
    first_bit_vector_sort && second_bit_vector_sort,
    "Shift expressions are expected to have bit vector operands.");
  const std::size_t first_width = first_bit_vector_sort->bit_width();
  const std::size_t second_width = second_bit_vector_sort->bit_width();
  if(first_width > second_width)
  {
    return factory(
      first_operand,
      extension_for_type(shift.op1().type())(first_width - second_width)(
        second_operand));
  }
  else if(first_width < second_width)
  {
    return factory(
      extension_for_type(shift.op0().type())(second_width - first_width)(
        first_operand),
      second_operand);
  }
  else
  {
    return factory(first_operand, second_operand);
  }
}

static smt_termt convert_expr_to_smt(
  const shift_exprt &shift,
  const sub_expression_mapt &converted)
{
  // TODO: Dispatch for rotation expressions. A `shift_exprt` can be a rotation.
  if(const auto left_shift = expr_try_dynamic_cast<shl_exprt>(shift))
  {
    return convert_to_smt_shift(
      smt_bit_vector_theoryt::shift_left, *left_shift, converted);
  }
  if(const auto right_logical_shift = expr_try_dynamic_cast<lshr_exprt>(shift))
  {
    return convert_to_smt_shift(
      smt_bit_vector_theoryt::logical_shift_right,
      *right_logical_shift,
      converted);
  }
  if(const auto right_arith_shift = expr_try_dynamic_cast<ashr_exprt>(shift))
  {
    return convert_to_smt_shift(
      smt_bit_vector_theoryt::arithmetic_shift_right,
      *right_arith_shift,
      converted);
  }
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for shift expression: " + shift.pretty());
}

static smt_termt convert_expr_to_smt(
  const with_exprt &with,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for with expression: " + with.pretty());
}

static smt_termt convert_expr_to_smt(
  const update_exprt &update,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for update expression: " + update.pretty());
}

static smt_termt convert_expr_to_smt(
  const member_exprt &member_extraction,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for member extraction expression: " +
    member_extraction.pretty());
}

static smt_termt convert_expr_to_smt(
  const is_dynamic_object_exprt &is_dynamic_object,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for is dynamic object expression: " +
    is_dynamic_object.pretty());
}

static smt_termt convert_expr_to_smt(
  const is_invalid_pointer_exprt &is_invalid_pointer,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for is invalid pointer expression: " +
    is_invalid_pointer.pretty());
}

static smt_termt convert_expr_to_smt(
  const string_constantt &is_invalid_pointer,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for is invalid pointer expression: " +
    is_invalid_pointer.pretty());
}

static smt_termt convert_expr_to_smt(
  const extractbit_exprt &extract_bit,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for extract bit expression: " +
    extract_bit.pretty());
}

static smt_termt convert_expr_to_smt(
  const extractbits_exprt &extract_bits,
  const sub_expression_mapt &converted)
{
  const smt_termt &from = converted.at(extract_bits.src());
  const auto upper_value = numeric_cast<std::size_t>(extract_bits.upper());
  const auto lower_value = numeric_cast<std::size_t>(extract_bits.lower());
  if(upper_value && lower_value)
    return smt_bit_vector_theoryt::extract(*upper_value, *lower_value)(from);
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for extract bits expression: " +
    extract_bits.pretty());
}

static smt_termt convert_expr_to_smt(
  const replication_exprt &replication,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for bit vector replication expression: " +
    replication.pretty());
}

static smt_termt convert_expr_to_smt(
  const byte_extract_exprt &byte_extraction,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for byte extract expression: " +
    byte_extraction.pretty());
}

static smt_termt convert_expr_to_smt(
  const byte_update_exprt &byte_update,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for byte update expression: " +
    byte_update.pretty());
}

static smt_termt convert_expr_to_smt(
  const abs_exprt &absolute_value_of,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for absolute value of expression: " +
    absolute_value_of.pretty());
}

static smt_termt convert_expr_to_smt(
  const isnan_exprt &is_nan_expr,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for is not a number expression: " +
    is_nan_expr.pretty());
}

static smt_termt convert_expr_to_smt(
  const isfinite_exprt &is_finite_expr,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for is finite expression: " +
    is_finite_expr.pretty());
}

static smt_termt convert_expr_to_smt(
  const isinf_exprt &is_infinite_expr,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for is infinite expression: " +
    is_infinite_expr.pretty());
}

static smt_termt convert_expr_to_smt(
  const isnormal_exprt &is_normal_expr,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for is infinite expression: " +
    is_normal_expr.pretty());
}

/// \brief
/// Constructs a term which is true if the most significant bit of \p input
/// is set.
static smt_termt most_significant_bit_is_set(const smt_termt &input)
{
  const auto bit_vector_sort = input.get_sort().cast<smt_bit_vector_sortt>();
  INVARIANT(
    bit_vector_sort,
    "Most significant bit can only be extracted from bit vector terms.");
  const size_t most_significant_bit_index = bit_vector_sort->bit_width() - 1;
  const auto extract_most_significant_bit = smt_bit_vector_theoryt::extract(
    most_significant_bit_index, most_significant_bit_index);
  return smt_core_theoryt::equal(
    extract_most_significant_bit(input), smt_bit_vector_constant_termt{1, 1});
}

static smt_termt convert_expr_to_smt(
  const plus_overflow_exprt &plus_overflow,
  const sub_expression_mapt &converted)
{
  const smt_termt &left = converted.at(plus_overflow.lhs());
  const smt_termt &right = converted.at(plus_overflow.rhs());
  if(operands_are_of_type<unsignedbv_typet>(plus_overflow))
  {
    const auto add_carry_bit = smt_bit_vector_theoryt::zero_extend(1);
    return most_significant_bit_is_set(
      smt_bit_vector_theoryt::add(add_carry_bit(left), add_carry_bit(right)));
  }
  if(operands_are_of_type<signedbv_typet>(plus_overflow))
  {
    // Overflow has occurred if the operands have the same sign and adding them
    // gives a result of the opposite sign.
    const smt_termt msb_left = most_significant_bit_is_set(left);
    const smt_termt msb_right = most_significant_bit_is_set(right);
    return smt_core_theoryt::make_and(
      smt_core_theoryt::equal(msb_left, msb_right),
      smt_core_theoryt::distinct(
        msb_left,
        most_significant_bit_is_set(smt_bit_vector_theoryt::add(left, right))));
  }
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for plus overflow expression: " +
    plus_overflow.pretty());
}

static smt_termt convert_expr_to_smt(
  const minus_overflow_exprt &minus_overflow,
  const sub_expression_mapt &converted)
{
  const smt_termt &left = converted.at(minus_overflow.lhs());
  const smt_termt &right = converted.at(minus_overflow.rhs());
  if(operands_are_of_type<unsignedbv_typet>(minus_overflow))
  {
    return smt_bit_vector_theoryt::unsigned_less_than(left, right);
  }
  if(operands_are_of_type<signedbv_typet>(minus_overflow))
  {
    // Overflow has occurred if the operands have the opposing signs and
    // subtracting them gives a result having the same signedness as the
    // right-hand operand. For example the following would be overflow for cases
    // for 8 bit wide bit vectors -
    //   -128 - 1 == 127
    //   127 - (-1) == -128
    const smt_termt msb_left = most_significant_bit_is_set(left);
    const smt_termt msb_right = most_significant_bit_is_set(right);
    return smt_core_theoryt::make_and(
      smt_core_theoryt::distinct(msb_left, msb_right),
      smt_core_theoryt::equal(
        msb_right,
        most_significant_bit_is_set(
          smt_bit_vector_theoryt::subtract(left, right))));
  }
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for minus overflow expression: " +
    minus_overflow.pretty());
}

static smt_termt convert_expr_to_smt(
  const mult_overflow_exprt &mult_overflow,
  const sub_expression_mapt &converted)
{
  PRECONDITION(mult_overflow.lhs().type() == mult_overflow.rhs().type());
  const auto &operand_type = mult_overflow.lhs().type();
  const smt_termt &left = converted.at(mult_overflow.lhs());
  const smt_termt &right = converted.at(mult_overflow.rhs());
  if(
    const auto unsigned_type =
      type_try_dynamic_cast<unsignedbv_typet>(operand_type))
  {
    const std::size_t width = unsigned_type->get_width();
    const auto extend = smt_bit_vector_theoryt::zero_extend(width);
    return smt_bit_vector_theoryt::unsigned_greater_than_or_equal(
      smt_bit_vector_theoryt::multiply(extend(left), extend(right)),
      smt_bit_vector_constant_termt{power(2, width), width * 2});
  }
  if(
    const auto signed_type =
      type_try_dynamic_cast<signedbv_typet>(operand_type))
  {
    const smt_termt msb_left = most_significant_bit_is_set(left);
    const smt_termt msb_right = most_significant_bit_is_set(right);
    const std::size_t width = signed_type->get_width();
    const auto extend = smt_bit_vector_theoryt::sign_extend(width);
    const auto multiplication =
      smt_bit_vector_theoryt::multiply(extend(left), extend(right));
    const auto too_large = smt_bit_vector_theoryt::signed_greater_than_or_equal(
      multiplication,
      smt_bit_vector_constant_termt{power(2, width - 1), width * 2});
    const auto too_small = smt_bit_vector_theoryt::signed_less_than(
      multiplication,
      smt_bit_vector_theoryt::negate(
        smt_bit_vector_constant_termt{power(2, width - 1), width * 2}));
    return smt_core_theoryt::if_then_else(
      smt_core_theoryt::equal(msb_left, msb_right), too_large, too_small);
  }
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for multiply overflow expression: " +
    mult_overflow.pretty());
}

static smt_termt convert_expr_to_smt(
  const shl_overflow_exprt &shl_overflow,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for shift left overflow expression: " +
    shl_overflow.pretty());
}

static smt_termt convert_expr_to_smt(
  const array_exprt &array_construction,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for array construction expression: " +
    array_construction.pretty());
}

static smt_termt convert_expr_to_smt(
  const literal_exprt &literal,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for literal expression: " + literal.pretty());
}

static smt_termt convert_expr_to_smt(
  const forall_exprt &for_all,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for for all expression: " + for_all.pretty());
}

static smt_termt convert_expr_to_smt(
  const exists_exprt &exists,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for exists expression: " + exists.pretty());
}

static smt_termt convert_expr_to_smt(
  const vector_exprt &vector,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for vector expression: " + vector.pretty());
}

static smt_termt
convert_expr_to_smt(const let_exprt &let, const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for let expression: " + let.pretty());
}

static smt_termt convert_expr_to_smt(
  const bswap_exprt &byte_swap,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for byte swap expression: " +
    byte_swap.pretty());
}

static smt_termt convert_expr_to_smt(
  const popcount_exprt &population_count,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for population count expression: " +
    population_count.pretty());
}

static smt_termt convert_expr_to_smt(
  const count_leading_zeros_exprt &count_leading_zeros,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for count leading zeros expression: " +
    count_leading_zeros.pretty());
}

static smt_termt convert_expr_to_smt(
  const count_trailing_zeros_exprt &count_trailing_zeros,
  const sub_expression_mapt &converted)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for byte swap expression: " +
    count_trailing_zeros.pretty());
}

static smt_termt dispatch_expr_to_smt_conversion(
  const exprt &expr,
  const sub_expression_mapt &converted,
  const smt_object_mapt &object_map)
{
  if(const auto symbol = expr_try_dynamic_cast<symbol_exprt>(expr))
  {
    return convert_expr_to_smt(*symbol);
  }
  if(const auto nondet = expr_try_dynamic_cast<nondet_symbol_exprt>(expr))
  {
    return convert_expr_to_smt(*nondet, converted);
  }
  if(const auto cast = expr_try_dynamic_cast<typecast_exprt>(expr))
  {
    return convert_expr_to_smt(*cast, converted);
  }
  if(
    const auto float_cast = expr_try_dynamic_cast<floatbv_typecast_exprt>(expr))
  {
    return convert_expr_to_smt(*float_cast, converted);
  }
  if(const auto struct_construction = expr_try_dynamic_cast<struct_exprt>(expr))
  {
    return convert_expr_to_smt(*struct_construction, converted);
  }
  if(const auto union_construction = expr_try_dynamic_cast<union_exprt>(expr))
  {
    return convert_expr_to_smt(*union_construction, converted);
  }
  if(const auto constant_literal = expr_try_dynamic_cast<constant_exprt>(expr))
  {
    return convert_expr_to_smt(*constant_literal);
  }
  if(
    const auto concatenation = expr_try_dynamic_cast<concatenation_exprt>(expr))
  {
    return convert_expr_to_smt(*concatenation, converted);
  }
  if(const auto bitwise_and_expr = expr_try_dynamic_cast<bitand_exprt>(expr))
  {
    return convert_expr_to_smt(*bitwise_and_expr, converted);
  }
  if(const auto bitwise_or_expr = expr_try_dynamic_cast<bitor_exprt>(expr))
  {
    return convert_expr_to_smt(*bitwise_or_expr, converted);
  }
  if(const auto bitwise_xor = expr_try_dynamic_cast<bitxor_exprt>(expr))
  {
    return convert_expr_to_smt(*bitwise_xor, converted);
  }
  if(const auto bitwise_not = expr_try_dynamic_cast<bitnot_exprt>(expr))
  {
    return convert_expr_to_smt(*bitwise_not, converted);
  }
  if(const auto unary_minus = expr_try_dynamic_cast<unary_minus_exprt>(expr))
  {
    return convert_expr_to_smt(*unary_minus, converted);
  }
  if(const auto unary_plus = expr_try_dynamic_cast<unary_plus_exprt>(expr))
  {
    return convert_expr_to_smt(*unary_plus, converted);
  }
  if(const auto is_negative = expr_try_dynamic_cast<sign_exprt>(expr))
  {
    return convert_expr_to_smt(*is_negative, converted);
  }
  if(const auto if_expression = expr_try_dynamic_cast<if_exprt>(expr))
  {
    return convert_expr_to_smt(*if_expression, converted);
  }
  if(const auto and_expression = expr_try_dynamic_cast<and_exprt>(expr))
  {
    return convert_expr_to_smt(*and_expression, converted);
  }
  if(const auto or_expression = expr_try_dynamic_cast<or_exprt>(expr))
  {
    return convert_expr_to_smt(*or_expression, converted);
  }
  if(const auto xor_expression = expr_try_dynamic_cast<xor_exprt>(expr))
  {
    return convert_expr_to_smt(*xor_expression, converted);
  }
  if(const auto implies = expr_try_dynamic_cast<implies_exprt>(expr))
  {
    return convert_expr_to_smt(*implies, converted);
  }
  if(const auto logical_not = expr_try_dynamic_cast<not_exprt>(expr))
  {
    return convert_expr_to_smt(*logical_not, converted);
  }
  if(const auto equal = expr_try_dynamic_cast<equal_exprt>(expr))
  {
    return convert_expr_to_smt(*equal, converted);
  }
  if(const auto not_equal = expr_try_dynamic_cast<notequal_exprt>(expr))
  {
    return convert_expr_to_smt(*not_equal, converted);
  }
  if(
    const auto float_equal =
      expr_try_dynamic_cast<ieee_float_equal_exprt>(expr))
  {
    return convert_expr_to_smt(*float_equal, converted);
  }
  if(
    const auto float_not_equal =
      expr_try_dynamic_cast<ieee_float_notequal_exprt>(expr))
  {
    return convert_expr_to_smt(*float_not_equal, converted);
  }
  if(
    const auto converted_relational =
      try_relational_conversion(expr, converted))
  {
    return *converted_relational;
  }
  if(const auto plus = expr_try_dynamic_cast<plus_exprt>(expr))
  {
    return convert_expr_to_smt(*plus, converted);
  }
  if(const auto minus = expr_try_dynamic_cast<minus_exprt>(expr))
  {
    return convert_expr_to_smt(*minus, converted);
  }
  if(const auto divide = expr_try_dynamic_cast<div_exprt>(expr))
  {
    return convert_expr_to_smt(*divide, converted);
  }
  if(
    const auto float_operation =
      expr_try_dynamic_cast<ieee_float_op_exprt>(expr))
  {
    return convert_expr_to_smt(*float_operation, converted);
  }
  if(const auto truncation_modulo = expr_try_dynamic_cast<mod_exprt>(expr))
  {
    return convert_expr_to_smt(*truncation_modulo, converted);
  }
  if(
    const auto euclidean_modulo =
      expr_try_dynamic_cast<euclidean_mod_exprt>(expr))
  {
    return convert_expr_to_smt(*euclidean_modulo, converted);
  }
  if(const auto multiply = expr_try_dynamic_cast<mult_exprt>(expr))
  {
    return convert_expr_to_smt(*multiply, converted);
  }
#if 0
  else if(expr.id() == ID_floatbv_rem)
  {
    convert_floatbv_rem(to_binary_expr(expr));
  }
#endif
  if(const auto address_of = expr_try_dynamic_cast<address_of_exprt>(expr))
  {
    return convert_expr_to_smt(*address_of, converted, object_map);
  }
  if(const auto array_of = expr_try_dynamic_cast<array_of_exprt>(expr))
  {
    return convert_expr_to_smt(*array_of, converted);
  }
  if(
    const auto array_comprehension =
      expr_try_dynamic_cast<array_comprehension_exprt>(expr))
  {
    return convert_expr_to_smt(*array_comprehension, converted);
  }
  if(const auto index = expr_try_dynamic_cast<index_exprt>(expr))
  {
    return convert_expr_to_smt(*index, converted);
  }
  if(const auto shift = expr_try_dynamic_cast<shift_exprt>(expr))
  {
    return convert_expr_to_smt(*shift, converted);
  }
  if(const auto with = expr_try_dynamic_cast<with_exprt>(expr))
  {
    return convert_expr_to_smt(*with, converted);
  }
  if(const auto update = expr_try_dynamic_cast<update_exprt>(expr))
  {
    return convert_expr_to_smt(*update, converted);
  }
  if(const auto member_extraction = expr_try_dynamic_cast<member_exprt>(expr))
  {
    return convert_expr_to_smt(*member_extraction, converted);
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
    return convert_expr_to_smt(*is_dynamic_object, converted);
  }
  if(
    const auto is_invalid_pointer =
      expr_try_dynamic_cast<is_invalid_pointer_exprt>(expr))
  {
    return convert_expr_to_smt(*is_invalid_pointer, converted);
  }
  if(const auto string_constant = expr_try_dynamic_cast<string_constantt>(expr))
  {
    return convert_expr_to_smt(*string_constant, converted);
  }
  if(const auto extract_bit = expr_try_dynamic_cast<extractbit_exprt>(expr))
  {
    return convert_expr_to_smt(*extract_bit, converted);
  }
  if(const auto extract_bits = expr_try_dynamic_cast<extractbits_exprt>(expr))
  {
    return convert_expr_to_smt(*extract_bits, converted);
  }
  if(const auto replication = expr_try_dynamic_cast<replication_exprt>(expr))
  {
    return convert_expr_to_smt(*replication, converted);
  }
  if(
    const auto byte_extraction =
      expr_try_dynamic_cast<byte_extract_exprt>(expr))
  {
    return convert_expr_to_smt(*byte_extraction, converted);
  }
  if(const auto byte_update = expr_try_dynamic_cast<byte_update_exprt>(expr))
  {
    return convert_expr_to_smt(*byte_update, converted);
  }
  if(const auto absolute_value_of = expr_try_dynamic_cast<abs_exprt>(expr))
  {
    return convert_expr_to_smt(*absolute_value_of, converted);
  }
  if(const auto is_nan_expr = expr_try_dynamic_cast<isnan_exprt>(expr))
  {
    return convert_expr_to_smt(*is_nan_expr, converted);
  }
  if(const auto is_finite_expr = expr_try_dynamic_cast<isfinite_exprt>(expr))
  {
    return convert_expr_to_smt(*is_finite_expr, converted);
  }
  if(const auto is_infinite_expr = expr_try_dynamic_cast<isinf_exprt>(expr))
  {
    return convert_expr_to_smt(*is_infinite_expr, converted);
  }
  if(const auto is_normal_expr = expr_try_dynamic_cast<isnormal_exprt>(expr))
  {
    return convert_expr_to_smt(*is_normal_expr, converted);
  }
  if(
    const auto plus_overflow = expr_try_dynamic_cast<plus_overflow_exprt>(expr))
  {
    return convert_expr_to_smt(*plus_overflow, converted);
  }
  if(
    const auto minus_overflow =
      expr_try_dynamic_cast<minus_overflow_exprt>(expr))
  {
    return convert_expr_to_smt(*minus_overflow, converted);
  }
  if(
    const auto mult_overflow = expr_try_dynamic_cast<mult_overflow_exprt>(expr))
  {
    return convert_expr_to_smt(*mult_overflow, converted);
  }
  if(const auto shl_overflow = expr_try_dynamic_cast<shl_overflow_exprt>(expr))
  {
    return convert_expr_to_smt(*shl_overflow, converted);
  }
  if(const auto array_construction = expr_try_dynamic_cast<array_exprt>(expr))
  {
    return convert_expr_to_smt(*array_construction, converted);
  }
  if(const auto literal = expr_try_dynamic_cast<literal_exprt>(expr))
  {
    return convert_expr_to_smt(*literal, converted);
  }
  if(const auto for_all = expr_try_dynamic_cast<forall_exprt>(expr))
  {
    return convert_expr_to_smt(*for_all, converted);
  }
  if(const auto exists = expr_try_dynamic_cast<exists_exprt>(expr))
  {
    return convert_expr_to_smt(*exists, converted);
  }
  if(const auto vector = expr_try_dynamic_cast<vector_exprt>(expr))
  {
    return convert_expr_to_smt(*vector, converted);
  }
#if 0
  else if(expr.id()==ID_object_size)
  {
    out << "|" << object_sizes[expr] << "|";
  }
#endif
  if(const auto let = expr_try_dynamic_cast<let_exprt>(expr))
  {
    return convert_expr_to_smt(*let, converted);
  }
  INVARIANT(
    expr.id() != ID_constraint_select_one,
    "constraint_select_one is not expected in smt conversion: " +
      expr.pretty());
  if(const auto byte_swap = expr_try_dynamic_cast<bswap_exprt>(expr))
  {
    return convert_expr_to_smt(*byte_swap, converted);
  }
  if(const auto population_count = expr_try_dynamic_cast<popcount_exprt>(expr))
  {
    return convert_expr_to_smt(*population_count, converted);
  }
  if(
    const auto count_leading_zeros =
      expr_try_dynamic_cast<count_leading_zeros_exprt>(expr))
  {
    return convert_expr_to_smt(*count_leading_zeros, converted);
  }
  if(
    const auto count_trailing_zeros =
      expr_try_dynamic_cast<count_trailing_zeros_exprt>(expr))
  {
    return convert_expr_to_smt(*count_trailing_zeros, converted);
  }

  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for unknown kind of expression: " +
    expr.pretty());
}

#ifndef CPROVER_INVARIANT_DO_NOT_CHECK
template <typename functiont>
struct at_scope_exitt
{
  explicit at_scope_exitt(functiont exit_function)
    : exit_function(exit_function)
  {
  }
  ~at_scope_exitt()
  {
    exit_function();
  }
  functiont exit_function;
};

template <typename functiont>
at_scope_exitt<functiont> at_scope_exit(functiont exit_function)
{
  return at_scope_exitt<functiont>(exit_function);
}
#endif

smt_termt
convert_expr_to_smt(const exprt &expr, const smt_object_mapt &object_map)
{
#ifndef CPROVER_INVARIANT_DO_NOT_CHECK
  static bool in_conversion = false;
  INVARIANT(
    !in_conversion,
    "Conversion of expr to smt should be non-recursive. "
    "Re-entrance found in conversion of " +
      expr.pretty(1, 0));
  in_conversion = true;
  const auto end_conversion = at_scope_exit([&]() { in_conversion = false; });
#endif
  sub_expression_mapt sub_expression_map;
  expr.visit_post([&](const exprt &expr) {
    const auto find_result = sub_expression_map.find(expr);
    if(find_result != sub_expression_map.cend())
      return;
    smt_termt term =
      dispatch_expr_to_smt_conversion(expr, sub_expression_map, object_map);
    sub_expression_map.emplace_hint(find_result, expr, std::move(term));
  });
  return std::move(sub_expression_map.at(expr));
}
