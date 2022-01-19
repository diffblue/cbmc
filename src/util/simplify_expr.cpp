/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_expr.h"

#include <algorithm>

#include "bitvector_expr.h"
#include "byte_operators.h"
#include "c_types.h"
#include "config.h"
#include "expr_util.h"
#include "fixedbv.h"
#include "floatbv_expr.h"
#include "invariant.h"
#include "mathematical_expr.h"
#include "namespace.h"
#include "pointer_expr.h"
#include "pointer_offset_size.h"
#include "pointer_offset_sum.h"
#include "rational.h"
#include "rational_tools.h"
#include "simplify_utils.h"
#include "std_expr.h"
#include "string_expr.h"

// #define DEBUGX

#ifdef DEBUGX
#include "format_expr.h"
#include <iostream>
#endif

#include "simplify_expr_class.h"

// #define USE_CACHE

#ifdef USE_CACHE
struct simplify_expr_cachet
{
public:
  #if 1
  typedef std::unordered_map<
    exprt, exprt, irep_full_hash, irep_full_eq> containert;
  #else
  typedef std::unordered_map<exprt, exprt, irep_hash> containert;
  #endif

  containert container_normal;

  containert &container()
  {
    return container_normal;
  }
};

simplify_expr_cachet simplify_expr_cache;
#endif

simplify_exprt::resultt<> simplify_exprt::simplify_abs(const abs_exprt &expr)
{
  if(expr.op().is_constant())
  {
    const typet &type = to_unary_expr(expr).op().type();

    if(type.id()==ID_floatbv)
    {
      ieee_floatt value(to_constant_expr(to_unary_expr(expr).op()));
      value.set_sign(false);
      return value.to_expr();
    }
    else if(type.id()==ID_signedbv ||
            type.id()==ID_unsignedbv)
    {
      auto value = numeric_cast<mp_integer>(to_unary_expr(expr).op());
      if(value.has_value())
      {
        if(*value >= 0)
        {
          return to_unary_expr(expr).op();
        }
        else
        {
          value->negate();
          return from_integer(*value, type);
        }
      }
    }
  }

  return unchanged(expr);
}

simplify_exprt::resultt<> simplify_exprt::simplify_sign(const sign_exprt &expr)
{
  if(expr.op().is_constant())
  {
    const typet &type = expr.op().type();

    if(type.id()==ID_floatbv)
    {
      ieee_floatt value(to_constant_expr(expr.op()));
      return make_boolean_expr(value.get_sign());
    }
    else if(type.id()==ID_signedbv ||
            type.id()==ID_unsignedbv)
    {
      const auto value = numeric_cast<mp_integer>(expr.op());
      if(value.has_value())
      {
        return make_boolean_expr(*value >= 0);
      }
    }
  }

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_popcount(const popcount_exprt &expr)
{
  const exprt &op = expr.op();

  if(op.is_constant())
  {
    const typet &op_type = op.type();

    if(op_type.id() == ID_signedbv || op_type.id() == ID_unsignedbv)
    {
      const auto width = to_bitvector_type(op_type).get_width();
      const auto &value = to_constant_expr(op).get_value();
      std::size_t result = 0;

      for(std::size_t i = 0; i < width; i++)
        if(get_bvrep_bit(value, width, i))
          result++;

      return from_integer(result, expr.type());
    }
  }

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_clz(const count_leading_zeros_exprt &expr)
{
  const auto const_bits_opt = expr2bits(
    expr.op(),
    config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN,
    ns);

  if(!const_bits_opt.has_value())
    return unchanged(expr);

  // expr2bits generates a bit string starting with the least-significant bit
  std::size_t n_leading_zeros = const_bits_opt->rfind('1');
  if(n_leading_zeros == std::string::npos)
  {
    if(!expr.zero_permitted())
      return unchanged(expr);

    n_leading_zeros = const_bits_opt->size();
  }
  else
    n_leading_zeros = const_bits_opt->size() - n_leading_zeros - 1;

  return from_integer(n_leading_zeros, expr.type());
}

simplify_exprt::resultt<>
simplify_exprt::simplify_ctz(const count_trailing_zeros_exprt &expr)
{
  const auto const_bits_opt = expr2bits(
    expr.op(),
    config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN,
    ns);

  if(!const_bits_opt.has_value())
    return unchanged(expr);

  // expr2bits generates a bit string starting with the least-significant bit
  std::size_t n_trailing_zeros = const_bits_opt->find('1');
  if(n_trailing_zeros == std::string::npos)
  {
    if(!expr.zero_permitted())
      return unchanged(expr);

    n_trailing_zeros = const_bits_opt->size();
  }

  return from_integer(n_trailing_zeros, expr.type());
}

/// Simplify String.endsWith function when arguments are constant
/// \param expr: the expression to simplify
/// \param ns: namespace
/// \return the modified expression or an unchanged expression
static simplify_exprt::resultt<> simplify_string_endswith(
  const function_application_exprt &expr,
  const namespacet &ns)
{
  const refined_string_exprt &s1 = to_string_expr(expr.arguments().at(0));
  const auto s1_data_opt = try_get_string_data_array(s1.content(), ns);

  if(!s1_data_opt)
    return simplify_exprt::unchanged(expr);

  const array_exprt &s1_data = s1_data_opt->get();
  const refined_string_exprt &s2 = to_string_expr(expr.arguments().at(1));
  const auto s2_data_opt = try_get_string_data_array(s2.content(), ns);

  if(!s2_data_opt)
    return simplify_exprt::unchanged(expr);

  const array_exprt &s2_data = s2_data_opt->get();
  const bool res = s2_data.operands().size() <= s1_data.operands().size() &&
                   std::equal(
                     s2_data.operands().rbegin(),
                     s2_data.operands().rend(),
                     s1_data.operands().rbegin());

  return from_integer(res ? 1 : 0, expr.type());
}

/// Simplify String.contains function when arguments are constant
static simplify_exprt::resultt<> simplify_string_contains(
  const function_application_exprt &expr,
  const namespacet &ns)
{
  // We want to get both arguments of any starts-with comparison, and
  // trace them back to the actual string instance. All variables on the
  // way must be constant for us to be sure this will work.
  auto &first_argument = to_string_expr(expr.arguments().at(0));
  auto &second_argument = to_string_expr(expr.arguments().at(1));

  const auto first_value_opt =
    try_get_string_data_array(first_argument.content(), ns);

  if(!first_value_opt)
  {
    return simplify_exprt::unchanged(expr);
  }

  const array_exprt &first_value = first_value_opt->get();

  const auto second_value_opt =
    try_get_string_data_array(second_argument.content(), ns);

  if(!second_value_opt)
  {
    return simplify_exprt::unchanged(expr);
  }

  const array_exprt &second_value = second_value_opt->get();

  // Is our 'contains' array directly contained in our target.
  const bool includes =
    std::search(
      first_value.operands().begin(),
      first_value.operands().end(),
      second_value.operands().begin(),
      second_value.operands().end()) != first_value.operands().end();

  return from_integer(includes ? 1 : 0, expr.type());
}

/// Simplify String.isEmpty function when arguments are constant
/// \param expr: the expression to simplify
/// \param ns: namespace
/// \return the modified expression or an unchanged expression
static simplify_exprt::resultt<> simplify_string_is_empty(
  const function_application_exprt &expr,
  const namespacet &ns)
{
  const function_application_exprt &function_app =
    to_function_application_expr(expr);
  const refined_string_exprt &s =
    to_string_expr(function_app.arguments().at(0));

  if(s.length().id() != ID_constant)
    return simplify_exprt::unchanged(expr);

  const auto numeric_length =
    numeric_cast_v<mp_integer>(to_constant_expr(s.length()));

  return from_integer(numeric_length == 0 ? 1 : 0, expr.type());
}

/// Simplify String.compareTo function when arguments are constant
///
/// The behaviour is similar to the implementation in OpenJDK:
/// http://hg.openjdk.java.net/jdk8/jdk8/jdk/file/687fd7c7986d/src/share/classes/java/lang/String.java#l1140
/// \param expr: the expression to simplify
/// \param ns: namespace
/// \return the modified expression or an unchanged expression
static simplify_exprt::resultt<> simplify_string_compare_to(
  const function_application_exprt &expr,
  const namespacet &ns)
{
  const refined_string_exprt &s1 = to_string_expr(expr.arguments().at(0));
  const auto s1_data_opt = try_get_string_data_array(s1.content(), ns);

  if(!s1_data_opt)
    return simplify_exprt::unchanged(expr);

  const refined_string_exprt &s2 = to_string_expr(expr.arguments().at(1));
  const auto s2_data_opt = try_get_string_data_array(s2.content(), ns);

  if(!s2_data_opt)
    return simplify_exprt::unchanged(expr);

  const array_exprt &s1_data = s1_data_opt->get();
  const array_exprt &s2_data = s2_data_opt->get();

  if(s1_data.operands() == s2_data.operands())
    return from_integer(0, expr.type());

  const mp_integer s1_size = s1_data.operands().size();
  const mp_integer s2_size = s2_data.operands().size();
  const bool first_shorter = s1_size < s2_size;
  const exprt::operandst &ops1 =
    first_shorter ? s1_data.operands() : s2_data.operands();
  const exprt::operandst &ops2 =
    first_shorter ? s2_data.operands() : s1_data.operands();
  auto it_pair = std::mismatch(ops1.begin(), ops1.end(), ops2.begin());

  if(it_pair.first == ops1.end())
    return from_integer(s1_size - s2_size, expr.type());

  const mp_integer char1 =
    numeric_cast_v<mp_integer>(to_constant_expr(*it_pair.first));
  const mp_integer char2 =
    numeric_cast_v<mp_integer>(to_constant_expr(*it_pair.second));

  return from_integer(
    first_shorter ? char1 - char2 : char2 - char1, expr.type());
}

/// Simplify String.indexOf function when arguments are constant
///
/// \param expr: the expression to simplify
/// \param ns: namespace
/// \param search_from_end: return the last instead of the first index
/// \return: the modified expression or an unchanged expression
static simplify_exprt::resultt<> simplify_string_index_of(
  const function_application_exprt &expr,
  const namespacet &ns,
  const bool search_from_end)
{
  std::size_t starting_index = 0;

  // Determine starting index for the comparison (if given)
  if(expr.arguments().size() == 3)
  {
    auto &starting_index_expr = expr.arguments().at(2);

    if(starting_index_expr.id() != ID_constant)
    {
      return simplify_exprt::unchanged(expr);
    }

    const mp_integer idx =
      numeric_cast_v<mp_integer>(to_constant_expr(starting_index_expr));

    // Negative indices are treated like 0
    if(idx > 0)
    {
      starting_index = numeric_cast_v<std::size_t>(idx);
    }
  }

  const refined_string_exprt &s1 = to_string_expr(expr.arguments().at(0));

  const auto s1_data_opt = try_get_string_data_array(s1.content(), ns);

  if(!s1_data_opt)
  {
    return simplify_exprt::unchanged(expr);
  }

  const array_exprt &s1_data = s1_data_opt->get();

  const auto search_string_size = s1_data.operands().size();
  if(starting_index >= search_string_size)
  {
    return from_integer(-1, expr.type());
  }

  unsigned long starting_offset =
    starting_index > 0 ? (search_string_size - 1) - starting_index : 0;
  if(can_cast_expr<refined_string_exprt>(expr.arguments().at(1)))
  {
    // Second argument is a string

    const refined_string_exprt &s2 = to_string_expr(expr.arguments().at(1));

    const auto s2_data_opt = try_get_string_data_array(s2.content(), ns);

    if(!s2_data_opt)
    {
      return simplify_exprt::unchanged(expr);
    }

    const array_exprt &s2_data = s2_data_opt->get();

    // Searching for empty string is a special case and is simply the
    // "always found at the first searched position. This needs to take into
    // account starting position and if you're starting from the beginning or
    // end.
    if(s2_data.operands().empty())
      return from_integer(
        search_from_end
          ? starting_index > 0 ? starting_index : search_string_size
          : 0,
        expr.type());

    if(search_from_end)
    {
      auto end = std::prev(s1_data.operands().end(), starting_offset);
      auto it = std::find_end(
        s1_data.operands().begin(),
        end,
        s2_data.operands().begin(),
        s2_data.operands().end());
      if(it != end)
        return from_integer(
          std::distance(s1_data.operands().begin(), it), expr.type());
    }
    else
    {
      auto it = std::search(
        std::next(s1_data.operands().begin(), starting_index),
        s1_data.operands().end(),
        s2_data.operands().begin(),
        s2_data.operands().end());

      if(it != s1_data.operands().end())
        return from_integer(
          std::distance(s1_data.operands().begin(), it), expr.type());
    }
  }
  else if(expr.arguments().at(1).id() == ID_constant)
  {
    // Second argument is a constant character

    const constant_exprt &c1 = to_constant_expr(expr.arguments().at(1));
    const auto c1_val = numeric_cast_v<mp_integer>(c1);

    auto pred = [&](const exprt &c2) {
      const auto c2_val = numeric_cast_v<mp_integer>(to_constant_expr(c2));

      return c1_val == c2_val;
    };

    if(search_from_end)
    {
      auto it = std::find_if(
        std::next(s1_data.operands().rbegin(), starting_offset),
        s1_data.operands().rend(),
        pred);
      if(it != s1_data.operands().rend())
        return from_integer(
          std::distance(s1_data.operands().begin(), it.base() - 1),
          expr.type());
    }
    else
    {
      auto it = std::find_if(
        std::next(s1_data.operands().begin(), starting_index),
        s1_data.operands().end(),
        pred);
      if(it != s1_data.operands().end())
        return from_integer(
          std::distance(s1_data.operands().begin(), it), expr.type());
    }
  }
  else
  {
    return simplify_exprt::unchanged(expr);
  }

  return from_integer(-1, expr.type());
}

/// Simplify String.charAt function when arguments are constant
///
/// \param expr: the expression to simplify
/// \param ns: namespace
/// \return: the modified expression or an unchanged expression
static simplify_exprt::resultt<> simplify_string_char_at(
  const function_application_exprt &expr,
  const namespacet &ns)
{
  if(expr.arguments().at(1).id() != ID_constant)
  {
    return simplify_exprt::unchanged(expr);
  }

  const auto &index = to_constant_expr(expr.arguments().at(1));

  const refined_string_exprt &s = to_string_expr(expr.arguments().at(0));

  const auto char_seq_opt = try_get_string_data_array(s.content(), ns);

  if(!char_seq_opt)
  {
    return simplify_exprt::unchanged(expr);
  }

  const array_exprt &char_seq = char_seq_opt->get();

  const auto i_opt = numeric_cast<std::size_t>(index);

  if(!i_opt || *i_opt >= char_seq.operands().size())
  {
    return simplify_exprt::unchanged(expr);
  }

  const auto &c = to_constant_expr(char_seq.operands().at(*i_opt));

  if(c.type() != expr.type())
  {
    return simplify_exprt::unchanged(expr);
  }

  return c;
}

/// Take the passed-in constant string array and lower-case every character.
static bool lower_case_string_expression(array_exprt &string_data)
{
  auto &operands = string_data.operands();
  for(auto &operand : operands)
  {
    auto &constant_value = to_constant_expr(operand);
    auto character = numeric_cast_v<unsigned int>(constant_value);

    // Can't guarantee matches against non-ASCII characters.
    if(character >= 128)
      return false;

    if(isalpha(character))
    {
      if(isupper(character))
        constant_value =
          from_integer(tolower(character), constant_value.type());
    }
  }

  return true;
}

/// Simplify String.equalsIgnorecase function when arguments are constant
///
/// \param expr: the expression to simplify
/// \param ns: namespace
/// \return: the modified expression or an unchanged expression
static simplify_exprt::resultt<> simplify_string_equals_ignore_case(
  const function_application_exprt &expr,
  const namespacet &ns)
{
  // We want to get both arguments of any starts-with comparison, and
  // trace them back to the actual string instance. All variables on the
  // way must be constant for us to be sure this will work.
  auto &first_argument = to_string_expr(expr.arguments().at(0));
  auto &second_argument = to_string_expr(expr.arguments().at(1));

  const auto first_value_opt =
    try_get_string_data_array(first_argument.content(), ns);

  if(!first_value_opt)
  {
    return simplify_exprt::unchanged(expr);
  }

  array_exprt first_value = first_value_opt->get();

  const auto second_value_opt =
    try_get_string_data_array(second_argument.content(), ns);

  if(!second_value_opt)
  {
    return simplify_exprt::unchanged(expr);
  }

  array_exprt second_value = second_value_opt->get();

  // Just lower-case both expressions.
  if(
    !lower_case_string_expression(first_value) ||
    !lower_case_string_expression(second_value))
    return simplify_exprt::unchanged(expr);

  bool is_equal = first_value == second_value;
  return from_integer(is_equal ? 1 : 0, expr.type());
}

/// Simplify String.startsWith function when arguments are constant
///
/// \param expr: the expression to simplify
/// \param ns: namespace
/// \return: the modified expression or an unchanged expression
static simplify_exprt::resultt<> simplify_string_startswith(
  const function_application_exprt &expr,
  const namespacet &ns)
{
  // We want to get both arguments of any starts-with comparison, and
  // trace them back to the actual string instance. All variables on the
  // way must be constant for us to be sure this will work.
  auto &first_argument = to_string_expr(expr.arguments().at(0));
  auto &second_argument = to_string_expr(expr.arguments().at(1));

  const auto first_value_opt =
    try_get_string_data_array(first_argument.content(), ns);

  if(!first_value_opt)
  {
    return simplify_exprt::unchanged(expr);
  }

  const array_exprt &first_value = first_value_opt->get();

  const auto second_value_opt =
    try_get_string_data_array(second_argument.content(), ns);

  if(!second_value_opt)
  {
    return simplify_exprt::unchanged(expr);
  }

  const array_exprt &second_value = second_value_opt->get();

  mp_integer offset_int = 0;
  if(expr.arguments().size() == 3)
  {
    auto &offset = expr.arguments()[2];
    if(offset.id() != ID_constant)
      return simplify_exprt::unchanged(expr);
    offset_int = numeric_cast_v<mp_integer>(to_constant_expr(offset));
  }

  // test whether second_value is a prefix of first_value
  bool is_prefix =
    offset_int >= 0 && mp_integer(first_value.operands().size()) >=
                         offset_int + second_value.operands().size();
  if(is_prefix)
  {
    exprt::operandst::const_iterator second_it =
      second_value.operands().begin();
    for(const auto &first_op : first_value.operands())
    {
      if(offset_int > 0)
        --offset_int;
      else if(second_it == second_value.operands().end())
        break;
      else if(first_op != *second_it)
      {
        is_prefix = false;
        break;
      }
      else
        ++second_it;
    }
  }

  return from_integer(is_prefix ? 1 : 0, expr.type());
}

simplify_exprt::resultt<> simplify_exprt::simplify_function_application(
  const function_application_exprt &expr)
{
  if(expr.function().id() == ID_lambda)
  {
    // expand the function application
    return to_lambda_expr(expr.function()).application(expr.arguments());
  }

  if(expr.function().id() != ID_symbol)
    return unchanged(expr);

  const irep_idt &func_id = to_symbol_expr(expr.function()).get_identifier();

  // String.startsWith() is used to implement String.equals() in the models
  // library
  if(func_id == ID_cprover_string_startswith_func)
  {
    return simplify_string_startswith(expr, ns);
  }
  else if(func_id == ID_cprover_string_endswith_func)
  {
    return simplify_string_endswith(expr, ns);
  }
  else if(func_id == ID_cprover_string_is_empty_func)
  {
    return simplify_string_is_empty(expr, ns);
  }
  else if(func_id == ID_cprover_string_compare_to_func)
  {
    return simplify_string_compare_to(expr, ns);
  }
  else if(func_id == ID_cprover_string_index_of_func)
  {
    return simplify_string_index_of(expr, ns, false);
  }
  else if(func_id == ID_cprover_string_char_at_func)
  {
    return simplify_string_char_at(expr, ns);
  }
  else if(func_id == ID_cprover_string_contains_func)
  {
    return simplify_string_contains(expr, ns);
  }
  else if(func_id == ID_cprover_string_last_index_of_func)
  {
    return simplify_string_index_of(expr, ns, true);
  }
  else if(func_id == ID_cprover_string_equals_ignore_case_func)
  {
    return simplify_string_equals_ignore_case(expr, ns);
  }

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_typecast(const typecast_exprt &expr)
{
  const typet &expr_type = expr.type();
  const typet &op_type = expr.op().type();

  // eliminate casts of infinity
  if(expr.op().id() == ID_infinity)
  {
    typet new_type=expr.type();
    exprt tmp = expr.op();
    tmp.type()=new_type;
    return std::move(tmp);
  }

  // casts from NULL to any integer
  if(
    op_type.id() == ID_pointer && expr.op().is_constant() &&
    to_constant_expr(expr.op()).get_value() == ID_NULL &&
    (expr_type.id() == ID_unsignedbv || expr_type.id() == ID_signedbv) &&
    config.ansi_c.NULL_is_zero)
  {
    return from_integer(0, expr_type);
  }

  // casts from pointer to integer
  // where width of integer >= width of pointer
  // (void*)(intX)expr -> (void*)expr
  if(
    expr_type.id() == ID_pointer && expr.op().id() == ID_typecast &&
    (op_type.id() == ID_signedbv || op_type.id() == ID_unsignedbv) &&
    to_bitvector_type(op_type).get_width() >=
      to_bitvector_type(expr_type).get_width())
  {
    auto new_expr = expr;
    new_expr.op() = to_typecast_expr(expr.op()).op();
    return changed(simplify_typecast(new_expr)); // rec. call
  }

  // eliminate redundant typecasts
  if(expr.type() == expr.op().type())
  {
    return expr.op();
  }

  // eliminate casts to proper bool
  if(expr_type.id()==ID_bool)
  {
    // rewrite (bool)x to x!=0
    binary_relation_exprt inequality(
      expr.op(),
      op_type.id() == ID_floatbv ? ID_ieee_float_notequal : ID_notequal,
      from_integer(0, op_type));
    inequality.add_source_location()=expr.source_location();
    return changed(simplify_node(inequality));
  }

  // eliminate casts from proper bool
  if(
    op_type.id() == ID_bool &&
    (expr_type.id() == ID_signedbv || expr_type.id() == ID_unsignedbv ||
     expr_type.id() == ID_c_bool || expr_type.id() == ID_c_bit_field))
  {
    // rewrite (T)(bool) to bool?1:0
    auto one = from_integer(1, expr_type);
    auto zero = from_integer(0, expr_type);
    exprt new_expr = if_exprt(expr.op(), std::move(one), std::move(zero));
    simplify_if_preorder(to_if_expr(new_expr));
    return new_expr;
  }

  // circular casts through types shorter than `int`
  if(op_type == signedbv_typet(32) && expr.op().id() == ID_typecast)
  {
    if(expr_type==c_bool_typet(8) ||
       expr_type==signedbv_typet(8) ||
       expr_type==signedbv_typet(16) ||
       expr_type==unsignedbv_typet(16))
    {
      // We checked that the id was ID_typecast in the enclosing `if`
      const auto &typecast = expr_checked_cast<typecast_exprt>(expr.op());
      if(typecast.op().type()==expr_type)
      {
        return typecast.op();
      }
    }
  }

  // eliminate casts to _Bool
  if(expr_type.id()==ID_c_bool &&
     op_type.id()!=ID_bool)
  {
    // rewrite (_Bool)x to (_Bool)(x!=0)
    exprt inequality = is_not_zero(expr.op(), ns);
    auto new_expr = expr;
    new_expr.op() = simplify_node(std::move(inequality));
    return changed(simplify_typecast(new_expr)); // recursive call
  }

  // eliminate typecasts from NULL
  if(
    expr_type.id() == ID_pointer && expr.op().is_constant() &&
    (to_constant_expr(expr.op()).get_value() == ID_NULL ||
     (expr.op().is_zero() && config.ansi_c.NULL_is_zero)))
  {
    exprt tmp = expr.op();
    tmp.type()=expr.type();
    to_constant_expr(tmp).set_value(ID_NULL);
    return std::move(tmp);
  }

  // eliminate duplicate pointer typecasts
  // (T1 *)(T2 *)x -> (T1 *)x
  if(
    expr_type.id() == ID_pointer && expr.op().id() == ID_typecast &&
    op_type.id() == ID_pointer)
  {
    auto new_expr = expr;
    new_expr.op() = to_typecast_expr(expr.op()).op();
    return changed(simplify_typecast(new_expr)); // recursive call
  }

  // casts from integer to pointer and back:
  // (int)(void *)int -> (int)(size_t)int
  if(
    (expr_type.id() == ID_signedbv || expr_type.id() == ID_unsignedbv) &&
    expr.op().id() == ID_typecast && expr.op().operands().size() == 1 &&
    op_type.id() == ID_pointer)
  {
    auto inner_cast = to_typecast_expr(expr.op());
    inner_cast.type() = size_type();

    auto outer_cast = expr;
    outer_cast.op() = simplify_typecast(inner_cast); // rec. call
    return changed(simplify_typecast(outer_cast));   // rec. call
  }

  // mildly more elaborate version of the above:
  // (int)((T*)0 + int) -> (int)(sizeof(T)*(size_t)int) if NULL is zero
  if(
    config.ansi_c.NULL_is_zero &&
    (expr_type.id() == ID_signedbv || expr_type.id() == ID_unsignedbv) &&
    op_type.id() == ID_pointer && expr.op().id() == ID_plus &&
    expr.op().operands().size() == 2)
  {
    const auto &op_plus_expr = to_plus_expr(expr.op());

    if(((op_plus_expr.op0().id() == ID_typecast &&
         to_typecast_expr(op_plus_expr.op0()).op().is_zero()) ||
        (op_plus_expr.op0().is_constant() &&
         to_constant_expr(op_plus_expr.op0()).get_value() == ID_NULL)))
    {
      auto sub_size =
        pointer_offset_size(to_pointer_type(op_type).base_type(), ns);
      if(sub_size.has_value())
      {
        auto new_expr = expr;
        exprt offset_expr =
          simplify_typecast(typecast_exprt(op_plus_expr.op1(), size_type()));

        // void*
        if(*sub_size == 0 || *sub_size == 1)
          new_expr.op() = offset_expr;
        else
        {
          new_expr.op() = simplify_mult(
            mult_exprt(from_integer(*sub_size, size_type()), offset_expr));
        }

        return changed(simplify_typecast(new_expr)); // rec. call
      }
    }
  }

  // Push a numerical typecast into various integer operations, i.e.,
  // (T)(x OP y) ---> (T)x OP (T)y
  //
  // Doesn't work for many, e.g., pointer difference, floating-point,
  // division, modulo.
  // Many operations fail if the width of T
  // is bigger than that of (x OP y). This includes ID_bitnot and
  // anything that might overflow, e.g., ID_plus.
  //
  if((expr_type.id()==ID_signedbv || expr_type.id()==ID_unsignedbv) &&
     (op_type.id()==ID_signedbv || op_type.id()==ID_unsignedbv))
  {
    bool enlarge=
      to_bitvector_type(expr_type).get_width()>
      to_bitvector_type(op_type).get_width();

    if(!enlarge)
    {
      irep_idt op_id = expr.op().id();

      if(op_id==ID_plus || op_id==ID_minus || op_id==ID_mult ||
         op_id==ID_unary_minus ||
         op_id==ID_bitxor || op_id==ID_bitor || op_id==ID_bitand)
      {
        exprt result = expr.op();

        if(
          result.operands().size() >= 1 &&
          to_multi_ary_expr(result).op0().type() == result.type())
        {
          result.type()=expr.type();

          Forall_operands(it, result)
          {
            auto new_operand = typecast_exprt(*it, expr.type());
            *it = simplify_typecast(new_operand); // recursive call
          }

          return changed(simplify_node(result)); // possibly recursive call
        }
      }
      else if(op_id==ID_ashr || op_id==ID_lshr || op_id==ID_shl)
      {
      }
    }
  }

  // Push a numerical typecast into pointer arithmetic
  // (T)(ptr + int) ---> (T)((size_t)ptr + sizeof(subtype)*(size_t)int)
  //
  if(
    (expr_type.id() == ID_signedbv || expr_type.id() == ID_unsignedbv) &&
    op_type.id() == ID_pointer && expr.op().id() == ID_plus)
  {
    const auto step =
      pointer_offset_size(to_pointer_type(op_type).base_type(), ns);

    if(step.has_value() && *step != 0)
    {
      const typet size_t_type(size_type());
      auto new_expr = expr;

      new_expr.op().type() = size_t_type;

      for(auto &op : new_expr.op().operands())
      {
        exprt new_op = simplify_typecast(typecast_exprt(op, size_t_type));
        if(op.type().id() != ID_pointer && *step > 1)
        {
          new_op =
            simplify_mult(mult_exprt(from_integer(*step, size_t_type), new_op));
        }
        op = std::move(new_op);
      }

      new_expr.op() = simplify_plus(to_plus_expr(new_expr.op()));

      return changed(simplify_typecast(new_expr)); // recursive call
    }
  }

  #if 0
  // (T)(a?b:c) --> a?(T)b:(T)c
  if(expr.op().id()==ID_if &&
     expr.op().operands().size()==3)
  {
    typecast_exprt tmp_op1(expr.op().op1(), expr_type);
    typecast_exprt tmp_op2(expr.op().op2(), expr_type);
    simplify_typecast(tmp_op1);
    simplify_typecast(tmp_op2);
    auto new_expr=if_exprt(expr.op().op0(), tmp_op1, tmp_op2, expr_type);
    simplify_if(new_expr);
    return std::move(new_expr);
  }
  #endif

  const irep_idt &expr_type_id=expr_type.id();
  const exprt &operand = expr.op();
  const irep_idt &op_type_id=op_type.id();

  if(operand.is_constant())
  {
    const irep_idt &value=to_constant_expr(operand).get_value();

    // preserve the sizeof type annotation
    typet c_sizeof_type=
      static_cast<const typet &>(operand.find(ID_C_c_sizeof_type));

    if(op_type_id==ID_integer ||
       op_type_id==ID_natural)
    {
      // from integer to ...

      mp_integer int_value=string2integer(id2string(value));

      if(expr_type_id==ID_bool)
      {
        return make_boolean_expr(int_value != 0);
      }

      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv ||
         expr_type_id==ID_c_enum ||
         expr_type_id==ID_c_bit_field ||
         expr_type_id==ID_integer)
      {
        return from_integer(int_value, expr_type);
      }
      else if(expr_type_id == ID_c_enum_tag)
      {
        const auto &c_enum_type = ns.follow_tag(to_c_enum_tag_type(expr_type));
        if(!c_enum_type.is_incomplete()) // possibly incomplete
        {
          exprt tmp = from_integer(int_value, c_enum_type);
          tmp.type() = expr_type; // we maintain the tag type
          return std::move(tmp);
        }
      }
    }
    else if(op_type_id==ID_rational)
    {
    }
    else if(op_type_id==ID_real)
    {
    }
    else if(op_type_id==ID_bool)
    {
      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv ||
         expr_type_id==ID_integer ||
         expr_type_id==ID_natural ||
         expr_type_id==ID_rational ||
         expr_type_id==ID_c_bool ||
         expr_type_id==ID_c_enum ||
         expr_type_id==ID_c_bit_field)
      {
        if(operand.is_true())
        {
          return from_integer(1, expr_type);
        }
        else if(operand.is_false())
        {
          return from_integer(0, expr_type);
        }
      }
      else if(expr_type_id==ID_c_enum_tag)
      {
        const auto &c_enum_type = ns.follow_tag(to_c_enum_tag_type(expr_type));
        if(!c_enum_type.is_incomplete()) // possibly incomplete
        {
          unsigned int_value = operand.is_true() ? 1u : 0u;
          exprt tmp=from_integer(int_value, c_enum_type);
          tmp.type()=expr_type; // we maintain the tag type
          return std::move(tmp);
        }
      }
      else if(expr_type_id==ID_pointer &&
              operand.is_false() &&
              config.ansi_c.NULL_is_zero)
      {
        return null_pointer_exprt(to_pointer_type(expr_type));
      }
    }
    else if(op_type_id==ID_unsignedbv ||
            op_type_id==ID_signedbv ||
            op_type_id==ID_c_bit_field ||
            op_type_id==ID_c_bool)
    {
      mp_integer int_value;

      if(to_integer(to_constant_expr(operand), int_value))
        return unchanged(expr);

      if(expr_type_id==ID_bool)
      {
        return make_boolean_expr(int_value != 0);
      }

      if(expr_type_id==ID_c_bool)
      {
        return from_integer(int_value != 0, expr_type);
      }

      if(expr_type_id==ID_integer)
      {
        return from_integer(int_value, expr_type);
      }

      if(expr_type_id==ID_natural)
      {
        if(int_value>=0)
        {
          return from_integer(int_value, expr_type);
        }
      }

      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv ||
         expr_type_id==ID_bv ||
         expr_type_id==ID_c_bit_field)
      {
        auto result = from_integer(int_value, expr_type);

        if(c_sizeof_type.is_not_nil())
          result.set(ID_C_c_sizeof_type, c_sizeof_type);

        return std::move(result);
      }

      if(expr_type_id==ID_c_enum_tag)
      {
        const auto &c_enum_type = ns.follow_tag(to_c_enum_tag_type(expr_type));
        if(!c_enum_type.is_incomplete()) // possibly incomplete
        {
          exprt tmp=from_integer(int_value, c_enum_type);
          tmp.type()=expr_type; // we maintain the tag type
          return std::move(tmp);
        }
      }

      if(expr_type_id==ID_c_enum)
      {
        return from_integer(int_value, expr_type);
      }

      if(expr_type_id==ID_fixedbv)
      {
        // int to float
        const fixedbv_typet &f_expr_type=
          to_fixedbv_type(expr_type);

        fixedbvt f;
        f.spec=fixedbv_spect(f_expr_type);
        f.from_integer(int_value);
        return f.to_expr();
      }

      if(expr_type_id==ID_floatbv)
      {
        // int to float
        const floatbv_typet &f_expr_type=
          to_floatbv_type(expr_type);

        ieee_floatt f(f_expr_type);
        f.from_integer(int_value);

        return f.to_expr();
      }

      if(expr_type_id==ID_rational)
      {
        rationalt r(int_value);
        return from_rational(r);
      }
    }
    else if(op_type_id==ID_fixedbv)
    {
      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv)
      {
        // cast from fixedbv to int
        fixedbvt f(to_constant_expr(expr.op()));
        return from_integer(f.to_integer(), expr_type);
      }
      else if(expr_type_id==ID_fixedbv)
      {
        // fixedbv to fixedbv
        fixedbvt f(to_constant_expr(expr.op()));
        f.round(fixedbv_spect(to_fixedbv_type(expr_type)));
        return f.to_expr();
      }
      else if(expr_type_id == ID_bv)
      {
        fixedbvt f{to_constant_expr(expr.op())};
        return from_integer(f.get_value(), expr_type);
      }
    }
    else if(op_type_id==ID_floatbv)
    {
      ieee_floatt f(to_constant_expr(expr.op()));

      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv)
      {
        // cast from float to int
        return from_integer(f.to_integer(), expr_type);
      }
      else if(expr_type_id==ID_floatbv)
      {
        // float to double or double to float
        f.change_spec(ieee_float_spect(to_floatbv_type(expr_type)));
        return f.to_expr();
      }
      else if(expr_type_id==ID_fixedbv)
      {
        fixedbvt fixedbv;
        fixedbv.spec=fixedbv_spect(to_fixedbv_type(expr_type));
        ieee_floatt factor(f.spec);
        factor.from_integer(power(2, fixedbv.spec.get_fraction_bits()));
        f*=factor;
        fixedbv.set_value(f.to_integer());
        return fixedbv.to_expr();
      }
      else if(expr_type_id == ID_bv)
      {
        return from_integer(f.pack(), expr_type);
      }
    }
    else if(op_type_id==ID_bv)
    {
      if(
        expr_type_id == ID_unsignedbv || expr_type_id == ID_signedbv ||
        expr_type_id == ID_c_enum || expr_type_id == ID_c_enum_tag ||
        expr_type_id == ID_c_bit_field)
      {
        const auto width = to_bv_type(op_type).get_width();
        const auto int_value = bvrep2integer(value, width, false);
        if(expr_type_id != ID_c_enum_tag)
          return from_integer(int_value, expr_type);
        else
        {
          c_enum_tag_typet tag_type = to_c_enum_tag_type(expr_type);
          auto result = from_integer(int_value, ns.follow_tag(tag_type));
          result.type() = tag_type;
          return std::move(result);
        }
      }
      else if(expr_type_id == ID_floatbv)
      {
        const auto width = to_bv_type(op_type).get_width();
        const auto int_value = bvrep2integer(value, width, false);
        ieee_floatt ieee_float{to_floatbv_type(expr_type)};
        ieee_float.unpack(int_value);
        return ieee_float.to_expr();
      }
      else if(expr_type_id == ID_fixedbv)
      {
        const auto width = to_bv_type(op_type).get_width();
        const auto int_value = bvrep2integer(value, width, false);
        fixedbvt fixedbv{fixedbv_spect{to_fixedbv_type(expr_type)}};
        fixedbv.set_value(int_value);
        return fixedbv.to_expr();
      }
    }
    else if(op_type_id==ID_c_enum_tag) // enum to int
    {
      const typet &base_type =
        ns.follow_tag(to_c_enum_tag_type(op_type)).underlying_type();
      if(base_type.id()==ID_signedbv || base_type.id()==ID_unsignedbv)
      {
        // enum constants use the representation of their base type
        auto new_expr = expr;
        new_expr.op().type() = base_type;
        return changed(simplify_typecast(new_expr)); // recursive call
      }
    }
    else if(op_type_id==ID_c_enum) // enum to int
    {
      const typet &base_type = to_c_enum_type(op_type).underlying_type();
      if(base_type.id()==ID_signedbv || base_type.id()==ID_unsignedbv)
      {
        // enum constants use the representation of their base type
        auto new_expr = expr;
        new_expr.op().type() = base_type;
        return changed(simplify_typecast(new_expr)); // recursive call
      }
    }
  }
  else if(operand.id()==ID_typecast) // typecast of typecast
  {
    // (T1)(T2)x ---> (T1)
    // where T1 has fewer bits than T2
    if(
      op_type_id == expr_type_id &&
      (expr_type_id == ID_unsignedbv || expr_type_id == ID_signedbv) &&
      to_bitvector_type(expr_type).get_width() <=
        to_bitvector_type(operand.type()).get_width())
    {
      auto new_expr = expr;
      new_expr.op() = to_typecast_expr(operand).op();
      // might enable further simplification
      return changed(simplify_typecast(new_expr)); // recursive call
    }
  }
  else if(operand.id()==ID_address_of)
  {
    const exprt &o=to_address_of_expr(operand).object();

    // turn &array into &array[0] when casting to pointer-to-element-type
    if(
      o.type().id() == ID_array &&
      expr_type == pointer_type(to_array_type(o.type()).element_type()))
    {
      auto result =
        address_of_exprt(index_exprt(o, from_integer(0, size_type())));

      return changed(simplify_address_of(result)); // recursive call
    }
  }

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_dereference(const dereference_exprt &expr)
{
  const exprt &pointer = expr.pointer();

  if(pointer.type().id()!=ID_pointer)
    return unchanged(expr);

  if(pointer.id()==ID_if && pointer.operands().size()==3)
  {
    const if_exprt &if_expr=to_if_expr(pointer);

    auto tmp_op1 = expr;
    tmp_op1.op() = if_expr.true_case();
    exprt tmp_op1_result = simplify_dereference(tmp_op1);

    auto tmp_op2 = expr;
    tmp_op2.op() = if_expr.false_case();
    exprt tmp_op2_result = simplify_dereference(tmp_op2);

    if_exprt tmp{if_expr.cond(), tmp_op1_result, tmp_op2_result};

    return changed(simplify_if(tmp));
  }

  if(pointer.id()==ID_address_of)
  {
    exprt tmp=to_address_of_expr(pointer).object();
    // one address_of is gone, try again
    return changed(simplify_rec(tmp));
  }
  // rewrite *(&a[0] + x) to a[x]
  else if(
    pointer.id() == ID_plus && pointer.operands().size() == 2 &&
    to_plus_expr(pointer).op0().id() == ID_address_of)
  {
    const auto &pointer_plus_expr = to_plus_expr(pointer);

    const address_of_exprt &address_of =
      to_address_of_expr(pointer_plus_expr.op0());

    if(address_of.object().id()==ID_index)
    {
      const index_exprt &old=to_index_expr(address_of.object());
      if(old.array().type().id() == ID_array)
      {
        index_exprt idx(
          old.array(),
          pointer_offset_sum(old.index(), pointer_plus_expr.op1()),
          to_array_type(old.array().type()).element_type());
        return changed(simplify_rec(idx));
      }
    }
  }

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_lambda(const lambda_exprt &expr)
{
  return unchanged(expr);
}

simplify_exprt::resultt<> simplify_exprt::simplify_with(const with_exprt &expr)
{
  bool no_change = true;

  if((expr.operands().size()%2)!=1)
    return unchanged(expr);

  // copy
  auto with_expr = expr;

  const typet old_type_followed = ns.follow(with_expr.old().type());

  // now look at first operand

  if(old_type_followed.id() == ID_struct)
  {
    if(with_expr.old().id() == ID_struct || with_expr.old().id() == ID_constant)
    {
      while(with_expr.operands().size() > 1)
      {
        const irep_idt &component_name =
          with_expr.where().get(ID_component_name);

        if(!to_struct_type(old_type_followed).has_component(component_name))
          return unchanged(expr);

        std::size_t number =
          to_struct_type(old_type_followed).component_number(component_name);

        if(number >= with_expr.old().operands().size())
          return unchanged(expr);

        with_expr.old().operands()[number].swap(with_expr.new_value());

        with_expr.operands().erase(++with_expr.operands().begin());
        with_expr.operands().erase(++with_expr.operands().begin());

        no_change = false;
      }
    }
  }
  else if(
    with_expr.old().type().id() == ID_array ||
    with_expr.old().type().id() == ID_vector)
  {
    if(
      with_expr.old().id() == ID_array || with_expr.old().id() == ID_constant ||
      with_expr.old().id() == ID_vector)
    {
      while(with_expr.operands().size() > 1)
      {
        const auto i = numeric_cast<mp_integer>(with_expr.where());

        if(!i.has_value())
          break;

        if(*i < 0 || *i >= with_expr.old().operands().size())
          break;

        with_expr.old().operands()[numeric_cast_v<std::size_t>(*i)].swap(
          with_expr.new_value());

        with_expr.operands().erase(++with_expr.operands().begin());
        with_expr.operands().erase(++with_expr.operands().begin());

        no_change = false;
      }
    }
  }

  if(with_expr.operands().size() == 1)
    return with_expr.old();

  if(no_change)
    return unchanged(expr);
  else
    return std::move(with_expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_update(const update_exprt &expr)
{
  // this is to push updates into (possibly nested) constants

  const exprt::operandst &designator = expr.designator();

  exprt updated_value = expr.old();
  exprt *value_ptr=&updated_value;

  for(const auto &e : designator)
  {
    const typet &value_ptr_type=ns.follow(value_ptr->type());

    if(e.id()==ID_index_designator &&
       value_ptr->id()==ID_array)
    {
      const auto i = numeric_cast<mp_integer>(to_index_designator(e).index());

      if(!i.has_value())
        return unchanged(expr);

      if(*i < 0 || *i >= value_ptr->operands().size())
        return unchanged(expr);

      value_ptr = &value_ptr->operands()[numeric_cast_v<std::size_t>(*i)];
    }
    else if(e.id()==ID_member_designator &&
            value_ptr->id()==ID_struct)
    {
      const irep_idt &component_name=
        e.get(ID_component_name);
      const struct_typet &value_ptr_struct_type =
        to_struct_type(value_ptr_type);
      if(!value_ptr_struct_type.has_component(component_name))
        return unchanged(expr);
      auto &designator_as_struct_expr = to_struct_expr(*value_ptr);
      value_ptr = &designator_as_struct_expr.component(component_name, ns);
      CHECK_RETURN(value_ptr->is_not_nil());
    }
    else
      return unchanged(expr); // give up, unknown designator
  }

  // found, done
  *value_ptr = expr.new_value();
  return updated_value;
}

simplify_exprt::resultt<> simplify_exprt::simplify_object(const exprt &expr)
{
  if(expr.id()==ID_plus)
  {
    if(expr.type().id()==ID_pointer)
    {
      // kill integers from sum
      for(auto &op : expr.operands())
        if(op.type().id() == ID_pointer)
          return changed(simplify_object(op)); // recursive call
    }
  }
  else if(expr.id()==ID_typecast)
  {
    auto const &typecast_expr = to_typecast_expr(expr);
    const typet &op_type = typecast_expr.op().type();

    if(op_type.id()==ID_pointer)
    {
      // cast from pointer to pointer
      return changed(simplify_object(typecast_expr.op())); // recursive call
    }
    else if(op_type.id()==ID_signedbv || op_type.id()==ID_unsignedbv)
    {
      // cast from integer to pointer

      // We do a bit of special treatment for (TYPE *)(a+(int)&o) and
      // (TYPE *)(a+(int)((T*)&o+x)), which are re-written to '&o'.

      const exprt &casted_expr = typecast_expr.op();
      if(casted_expr.id() == ID_plus && casted_expr.operands().size() == 2)
      {
        const auto &plus_expr = to_plus_expr(casted_expr);

        const exprt &cand = plus_expr.op0().id() == ID_typecast
                              ? plus_expr.op0()
                              : plus_expr.op1();

        if(cand.id() == ID_typecast)
        {
          const auto &typecast_op = to_typecast_expr(cand).op();

          if(typecast_op.id() == ID_address_of)
          {
            return typecast_op;
          }
          else if(
            typecast_op.id() == ID_plus && typecast_op.operands().size() == 2 &&
            to_plus_expr(typecast_op).op0().id() == ID_typecast &&
            to_typecast_expr(to_plus_expr(typecast_op).op0()).op().id() ==
              ID_address_of)
          {
            return to_typecast_expr(to_plus_expr(typecast_op).op0()).op();
          }
        }
      }
    }
  }
  else if(expr.id()==ID_address_of)
  {
    const auto &object = to_address_of_expr(expr).object();

    if(object.id() == ID_index)
    {
      // &some[i] -> &some
      address_of_exprt new_expr(to_index_expr(object).array());
      return changed(simplify_object(new_expr)); // recursion
    }
    else if(object.id() == ID_member)
    {
      // &some.f -> &some
      address_of_exprt new_expr(to_member_expr(object).compound());
      return changed(simplify_object(new_expr)); // recursion
    }
  }

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_byte_extract(const byte_extract_exprt &expr)
{
  // lift up any ID_if on the object
  if(expr.op().id()==ID_if)
  {
    if_exprt if_expr=lift_if(expr, 0);
    if_expr.true_case() =
      simplify_byte_extract(to_byte_extract_expr(if_expr.true_case()));
    if_expr.false_case() =
      simplify_byte_extract(to_byte_extract_expr(if_expr.false_case()));
    return changed(simplify_if(if_expr));
  }

  const auto el_size = pointer_offset_bits(expr.type(), ns);
  if(el_size.has_value() && *el_size < 0)
    return unchanged(expr);

  // byte_extract(byte_extract(root, offset1), offset2) =>
  // byte_extract(root, offset1+offset2)
  if(expr.op().id()==expr.id())
  {
    auto tmp = expr;

    tmp.offset() = simplify_plus(
      plus_exprt(to_byte_extract_expr(expr.op()).offset(), expr.offset()));
    tmp.op() = to_byte_extract_expr(expr.op()).op();

    return changed(simplify_byte_extract(tmp)); // recursive call
  }

  // byte_extract(byte_update(root, offset, value), offset) =>
  // value
  if(
    ((expr.id() == ID_byte_extract_big_endian &&
      expr.op().id() == ID_byte_update_big_endian) ||
     (expr.id() == ID_byte_extract_little_endian &&
      expr.op().id() == ID_byte_update_little_endian)) &&
    expr.offset() == to_byte_update_expr(as_const(expr).op()).offset())
  {
    const auto &op_byte_update = to_byte_update_expr(expr.op());

    if(expr.type() == op_byte_update.value().type())
    {
      return op_byte_update.value();
    }
    else if(
      el_size.has_value() &&
      *el_size <= pointer_offset_bits(op_byte_update.value().type(), ns))
    {
      auto tmp = expr;
      tmp.op() = op_byte_update.value();
      tmp.offset() = from_integer(0, expr.offset().type());

      return changed(simplify_byte_extract(tmp)); // recursive call
    }
  }

  // the following require a constant offset
  auto offset = numeric_cast<mp_integer>(expr.offset());
  if(!offset.has_value() || *offset < 0)
    return unchanged(expr);

  // don't do any of the following if endianness doesn't match, as
  // bytes need to be swapped
  if(
    *offset == 0 && ((expr.id() == ID_byte_extract_little_endian &&
                      config.ansi_c.endianness ==
                        configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN) ||
                     (expr.id() == ID_byte_extract_big_endian &&
                      config.ansi_c.endianness ==
                        configt::ansi_ct::endiannesst::IS_BIG_ENDIAN)))
  {
    // byte extract of full object is object
    if(expr.type() == expr.op().type())
    {
      return expr.op();
    }
    else if(
      expr.type().id() == ID_pointer && expr.op().type().id() == ID_pointer)
    {
      return typecast_exprt(expr.op(), expr.type());
    }
  }

  // no proper simplification for expr.type()==void
  // or types of unknown size
  if(!el_size.has_value() || *el_size == 0)
    return unchanged(expr);

  if(expr.op().id()==ID_array_of &&
     to_array_of_expr(expr.op()).op().id()==ID_constant)
  {
    const auto const_bits_opt = expr2bits(
      to_array_of_expr(expr.op()).op(),
      config.ansi_c.endianness ==
        configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN,
      ns);

    if(!const_bits_opt.has_value())
      return unchanged(expr);

    std::string const_bits=const_bits_opt.value();

    DATA_INVARIANT(!const_bits.empty(), "bit representation must be non-empty");

    // double the string until we have sufficiently many bits
    while(mp_integer(const_bits.size()) < *offset * 8 + *el_size)
      const_bits+=const_bits;

    std::string el_bits = std::string(
      const_bits,
      numeric_cast_v<std::size_t>(*offset * 8),
      numeric_cast_v<std::size_t>(*el_size));

    auto tmp = bits2expr(
      el_bits, expr.type(), expr.id() == ID_byte_extract_little_endian, ns);

    if(tmp.has_value())
      return std::move(*tmp);
  }

  // in some cases we even handle non-const array_of
  if(
    expr.op().id() == ID_array_of && (*offset * 8) % (*el_size) == 0 &&
    *el_size <=
      pointer_offset_bits(to_array_of_expr(expr.op()).what().type(), ns))
  {
    auto tmp = expr;
    tmp.op() = simplify_index(index_exprt(expr.op(), expr.offset()));
    tmp.offset() = from_integer(0, expr.offset().type());
    return changed(simplify_byte_extract(tmp));
  }

  // extract bits of a constant
  const auto bits =
    expr2bits(expr.op(), expr.id() == ID_byte_extract_little_endian, ns);

  // make sure we don't lose bits with structs containing flexible array members
  const bool struct_has_flexible_array_member = has_subtype(
    expr.type(),
    [&](const typet &type) {
      if(type.id() != ID_struct && type.id() != ID_struct_tag)
        return false;

      const struct_typet &st = to_struct_type(ns.follow(type));
      const auto &comps = st.components();
      if(comps.empty() || comps.back().type().id() != ID_array)
        return false;

      const auto size =
        numeric_cast<mp_integer>(to_array_type(comps.back().type()).size());
      return !size.has_value() || *size <= 1;
    },
    ns);
  if(
    bits.has_value() && mp_integer(bits->size()) >= *el_size + *offset * 8 &&
    !struct_has_flexible_array_member)
  {
    std::string bits_cut = std::string(
      bits.value(),
      numeric_cast_v<std::size_t>(*offset * 8),
      numeric_cast_v<std::size_t>(*el_size));

    auto tmp = bits2expr(
      bits_cut, expr.type(), expr.id() == ID_byte_extract_little_endian, ns);

    if(tmp.has_value())
      return std::move(*tmp);
  }

  // push byte extracts into struct or union expressions, just like
  // lower_byte_extract does (this is the same code, except recursive calls use
  // simplify rather than lower_byte_extract)
  if(expr.op().id() == ID_struct || expr.op().id() == ID_union)
  {
    if(expr.type().id() == ID_struct || expr.type().id() == ID_struct_tag)
    {
      const struct_typet &struct_type = to_struct_type(ns.follow(expr.type()));
      const struct_typet::componentst &components = struct_type.components();

      bool failed = false;
      struct_exprt s({}, expr.type());

      for(const auto &comp : components)
      {
        auto component_bits = pointer_offset_bits(comp.type(), ns);

        // the next member would be misaligned, abort
        if(
          !component_bits.has_value() || *component_bits == 0 ||
          *component_bits % 8 != 0)
        {
          failed = true;
          break;
        }

        auto member_offset_opt =
          member_offset_expr(struct_type, comp.get_name(), ns);

        if(!member_offset_opt.has_value())
        {
          failed = true;
          break;
        }

        exprt new_offset = simplify_rec(
          plus_exprt{expr.offset(),
                     typecast_exprt::conditional_cast(
                       member_offset_opt.value(), expr.offset().type())});

        byte_extract_exprt tmp = expr;
        tmp.type() = comp.type();
        tmp.offset() = new_offset;

        s.add_to_operands(simplify_byte_extract(tmp));
      }

      if(!failed)
        return s;
    }
    else if(expr.type().id() == ID_union || expr.type().id() == ID_union_tag)
    {
      const union_typet &union_type = to_union_type(ns.follow(expr.type()));
      auto widest_member_opt = union_type.find_widest_union_component(ns);
      if(widest_member_opt.has_value())
      {
        byte_extract_exprt be = expr;
        be.type() = widest_member_opt->first.type();
        return union_exprt{widest_member_opt->first.get_name(),
                           simplify_byte_extract(be),
                           expr.type()};
      }
    }
  }

  // try to refine it down to extracting from a member or an index in an array
  auto subexpr =
    get_subexpression_at_offset(expr.op(), *offset, expr.type(), ns);
  if(!subexpr.has_value() || subexpr.value() == expr)
    return unchanged(expr);

  return changed(simplify_rec(subexpr.value())); // recursive call
}

simplify_exprt::resultt<>
simplify_exprt::simplify_byte_update(const byte_update_exprt &expr)
{
  // byte_update(byte_update(root, offset, value), offset, value2) =>
  // byte_update(root, offset, value2)
  if(
    expr.id() == expr.op().id() &&
    expr.offset() == to_byte_update_expr(expr.op()).offset() &&
    expr.value().type() == to_byte_update_expr(expr.op()).value().type())
  {
    auto tmp = expr;
    tmp.set_op(to_byte_update_expr(expr.op()).op());
    return std::move(tmp);
  }

  const exprt &root = expr.op();
  const exprt &offset = expr.offset();
  const exprt &value = expr.value();
  const auto val_size = pointer_offset_bits(value.type(), ns);
  const auto root_size = pointer_offset_bits(root.type(), ns);

  // byte update of full object is byte_extract(new value)
  if(
    offset.is_zero() && val_size.has_value() && *val_size > 0 &&
    root_size.has_value() && *root_size > 0 && *val_size >= *root_size)
  {
    byte_extract_exprt be(
      expr.id()==ID_byte_update_little_endian ?
        ID_byte_extract_little_endian :
        ID_byte_extract_big_endian,
      value, offset, expr.type());

    return changed(simplify_byte_extract(be));
  }

  // update bits in a constant
  const auto offset_int = numeric_cast<mp_integer>(offset);
  if(
    root_size.has_value() && *root_size >= 0 && val_size.has_value() &&
    *val_size >= 0 && offset_int.has_value() && *offset_int >= 0 &&
    *offset_int * 8 + *val_size <= *root_size)
  {
    auto root_bits =
      expr2bits(root, expr.id() == ID_byte_update_little_endian, ns);

    if(root_bits.has_value())
    {
      const auto val_bits =
        expr2bits(value, expr.id() == ID_byte_update_little_endian, ns);

      if(val_bits.has_value())
      {
        root_bits->replace(
          numeric_cast_v<std::size_t>(*offset_int * 8),
          numeric_cast_v<std::size_t>(*val_size),
          *val_bits);

        auto tmp = bits2expr(
          *root_bits,
          expr.type(),
          expr.id() == ID_byte_update_little_endian,
          ns);

        if(tmp.has_value())
          return std::move(*tmp);
      }
    }
  }

  /*
   * byte_update(root, offset,
   *             extract(root, offset) WITH component:=value)
   * =>
   * byte_update(root, offset + component offset,
   *             value)
   */

  if(expr.id()!=ID_byte_update_little_endian)
    return unchanged(expr);

  if(value.id()==ID_with)
  {
    const with_exprt &with=to_with_expr(value);

    if(with.old().id()==ID_byte_extract_little_endian)
    {
      const byte_extract_exprt &extract=to_byte_extract_expr(with.old());

      /* the simplification can be used only if
         root and offset of update and extract
         are the same */
      if(!(root==extract.op()))
        return unchanged(expr);
      if(!(offset==extract.offset()))
        return unchanged(expr);

      const typet &tp=ns.follow(with.type());
      if(tp.id()==ID_struct)
      {
        const struct_typet &struct_type=to_struct_type(tp);
        const irep_idt &component_name=with.where().get(ID_component_name);
        const typet &c_type = struct_type.get_component(component_name).type();

        // is this a bit field?
        if(c_type.id() == ID_c_bit_field || c_type.id() == ID_bool)
        {
          // don't touch -- might not be byte-aligned
        }
        else
        {
          // new offset = offset + component offset
          auto i = member_offset(struct_type, component_name, ns);
          if(i.has_value())
          {
            exprt compo_offset = from_integer(*i, offset.type());
            plus_exprt new_offset(offset, compo_offset);
            exprt new_value(with.new_value());
            auto tmp = expr;
            tmp.set_offset(simplify_node(std::move(new_offset)));
            tmp.set_value(std::move(new_value));
            return changed(simplify_byte_update(tmp)); // recursive call
          }
        }
      }
      else if(tp.id()==ID_array)
      {
        auto i = pointer_offset_size(to_array_type(tp).element_type(), ns);
        if(i.has_value())
        {
          const exprt &index=with.where();
          exprt index_offset =
            simplify_mult(mult_exprt(index, from_integer(*i, index.type())));

          // index_offset may need a typecast
          if(offset.type() != index.type())
          {
            index_offset =
              simplify_typecast(typecast_exprt(index_offset, offset.type()));
          }

          plus_exprt new_offset(offset, index_offset);
          exprt new_value(with.new_value());
          auto tmp = expr;
          tmp.set_offset(simplify_plus(std::move(new_offset)));
          tmp.set_value(std::move(new_value));
          return changed(simplify_byte_update(tmp)); // recursive call
        }
      }
    }
  }

  // the following require a constant offset
  if(!offset_int.has_value() || *offset_int < 0)
    return unchanged(expr);

  const typet &op_type=ns.follow(root.type());

  // size must be known
  if(!val_size.has_value() || *val_size == 0)
    return unchanged(expr);

  // Are we updating (parts of) a struct? Do individual member updates
  // instead, unless there are non-byte-sized bit fields
  if(op_type.id()==ID_struct)
  {
    exprt result_expr;
    result_expr.make_nil();

    auto update_size = pointer_offset_size(value.type(), ns);

    const struct_typet &struct_type=
      to_struct_type(op_type);
    const struct_typet::componentst &components=
      struct_type.components();

    for(const auto &component : components)
    {
      auto m_offset = member_offset(struct_type, component.get_name(), ns);

      auto m_size_bits = pointer_offset_bits(component.type(), ns);

      // can we determine the current offset?
      if(!m_offset.has_value())
      {
        result_expr.make_nil();
        break;
      }

      // is it a byte-sized member?
      if(!m_size_bits.has_value() || *m_size_bits == 0 || (*m_size_bits) % 8 != 0)
      {
        result_expr.make_nil();
        break;
      }

      mp_integer m_size_bytes = (*m_size_bits) / 8;

      // is that member part of the update?
      if(*m_offset + m_size_bytes <= *offset_int)
        continue;
      // are we done updating?
      else if(
        update_size.has_value() && *update_size > 0 &&
        *m_offset >= *offset_int + *update_size)
      {
        break;
      }

      if(result_expr.is_nil())
        result_expr = as_const(expr).op();

      exprt member_name(ID_member_name);
      member_name.set(ID_component_name, component.get_name());
      result_expr=with_exprt(result_expr, member_name, nil_exprt());

      // are we updating on member boundaries?
      if(
        *m_offset < *offset_int ||
        (*m_offset == *offset_int && update_size.has_value() &&
         *update_size > 0 && m_size_bytes > *update_size))
      {
        byte_update_exprt v(
          ID_byte_update_little_endian,
          member_exprt(root, component.get_name(), component.type()),
          from_integer(*offset_int - *m_offset, offset.type()),
          value);

        to_with_expr(result_expr).new_value().swap(v);
      }
      else if(
        update_size.has_value() && *update_size > 0 &&
        *m_offset + m_size_bytes > *offset_int + *update_size)
      {
        // we don't handle this for the moment
        result_expr.make_nil();
        break;
      }
      else
      {
        byte_extract_exprt v(
          ID_byte_extract_little_endian,
          value,
          from_integer(*m_offset - *offset_int, offset.type()),
          component.type());

        to_with_expr(result_expr).new_value().swap(v);
      }
    }

    if(result_expr.is_not_nil())
      return changed(simplify_rec(result_expr));
  }

  // replace elements of array or struct expressions, possibly using
  // byte_extract
  if(root.id()==ID_array)
  {
    auto el_size =
      pointer_offset_bits(to_type_with_subtype(op_type).subtype(), ns);

    if(!el_size.has_value() || *el_size == 0 ||
       (*el_size) % 8 != 0 || (*val_size) % 8 != 0)
    {
      return unchanged(expr);
    }

    exprt result=root;

    mp_integer m_offset_bits=0, val_offset=0;
    Forall_operands(it, result)
    {
      if(*offset_int * 8 + (*val_size) <= m_offset_bits)
        break;

      if(*offset_int * 8 < m_offset_bits + *el_size)
      {
        mp_integer bytes_req = (m_offset_bits + *el_size) / 8 - *offset_int;
        bytes_req-=val_offset;
        if(val_offset + bytes_req > (*val_size) / 8)
          bytes_req = (*val_size) / 8 - val_offset;

        byte_extract_exprt new_val(
          ID_byte_extract_little_endian,
          value,
          from_integer(val_offset, offset.type()),
          array_typet(
            unsignedbv_typet(8), from_integer(bytes_req, offset.type())));

        *it = byte_update_exprt(
          expr.id(),
          *it,
          from_integer(
            *offset_int + val_offset - m_offset_bits / 8, offset.type()),
          new_val);

        *it = simplify_rec(*it); // recursive call

        val_offset+=bytes_req;
      }

      m_offset_bits += *el_size;
    }

    return std::move(result);
  }

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_complex(const unary_exprt &expr)
{
  if(expr.id() == ID_complex_real)
  {
    auto &complex_real_expr = to_complex_real_expr(expr);

    if(complex_real_expr.op().id() == ID_complex)
      return to_complex_expr(complex_real_expr.op()).real();
  }
  else if(expr.id() == ID_complex_imag)
  {
    auto &complex_imag_expr = to_complex_imag_expr(expr);

    if(complex_imag_expr.op().id() == ID_complex)
      return to_complex_expr(complex_imag_expr.op()).imag();
  }

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_overflow_binary(const binary_overflow_exprt &expr)
{
  // zero is a neutral element for all operations supported here
  if(
    expr.op1().is_zero() ||
    (expr.op0().is_zero() && expr.id() != ID_overflow_minus))
  {
    return false_exprt{};
  }

  // we only handle the case of same operand types
  if(expr.op0().type() != expr.op1().type())
    return unchanged(expr);

  // catch some cases over mathematical types
  const irep_idt &op_type_id = expr.op0().type().id();
  if(
    op_type_id == ID_integer || op_type_id == ID_rational ||
    op_type_id == ID_real)
  {
    return false_exprt{};
  }

  if(op_type_id == ID_natural && expr.id() != ID_overflow_minus)
    return false_exprt{};

  // we only handle constants over signedbv/unsignedbv for the remaining cases
  if(op_type_id != ID_signedbv && op_type_id != ID_unsignedbv)
    return unchanged(expr);

  if(!expr.op0().is_constant() || !expr.op1().is_constant())
    return unchanged(expr);

  const auto op0_value = numeric_cast<mp_integer>(expr.op0());
  const auto op1_value = numeric_cast<mp_integer>(expr.op1());
  if(!op0_value.has_value() || !op1_value.has_value())
    return unchanged(expr);

  mp_integer no_overflow_result;
  if(expr.id() == ID_overflow_plus)
    no_overflow_result = *op0_value + *op1_value;
  else if(expr.id() == ID_overflow_minus)
    no_overflow_result = *op0_value - *op1_value;
  else if(expr.id() == ID_overflow_mult)
    no_overflow_result = *op0_value * *op1_value;
  else if(expr.id() == ID_overflow_shl)
    no_overflow_result = *op0_value << *op1_value;
  else
    UNREACHABLE;

  const std::size_t width = to_bitvector_type(expr.op0().type()).get_width();
  const integer_bitvector_typet bv_type{op_type_id, width};
  if(
    no_overflow_result < bv_type.smallest() ||
    no_overflow_result > bv_type.largest())
  {
    return true_exprt{};
  }
  else
    return false_exprt{};
}

simplify_exprt::resultt<>
simplify_exprt::simplify_overflow_unary(const unary_overflow_exprt &expr)
{
  // zero is a neutral element for all operations supported here
  if(expr.op().is_zero())
    return false_exprt{};

  // catch some cases over mathematical types
  const irep_idt &op_type_id = expr.op().type().id();
  if(
    op_type_id == ID_integer || op_type_id == ID_rational ||
    op_type_id == ID_real)
  {
    return false_exprt{};
  }

  if(op_type_id == ID_natural)
    return true_exprt{};

  // we only handle constants over signedbv/unsignedbv for the remaining cases
  if(op_type_id != ID_signedbv && op_type_id != ID_unsignedbv)
    return unchanged(expr);

  if(!expr.op().is_constant())
    return unchanged(expr);

  const auto op_value = numeric_cast<mp_integer>(expr.op());
  if(!op_value.has_value())
    return unchanged(expr);

  mp_integer no_overflow_result;
  if(expr.id() == ID_overflow_unary_minus)
    no_overflow_result = -*op_value;
  else
    UNREACHABLE;

  const std::size_t width = to_bitvector_type(expr.op().type()).get_width();
  const integer_bitvector_typet bv_type{op_type_id, width};
  if(
    no_overflow_result < bv_type.smallest() ||
    no_overflow_result > bv_type.largest())
  {
    return true_exprt{};
  }
  else
    return false_exprt{};
}

bool simplify_exprt::simplify_node_preorder(exprt &expr)
{
  bool result=true;

  // The ifs below could one day be replaced by a switch()

  if(expr.id()==ID_address_of)
  {
    // the argument of this expression needs special treatment
  }
  else if(expr.id()==ID_if)
    result=simplify_if_preorder(to_if_expr(expr));
  else
  {
    if(expr.has_operands())
    {
      Forall_operands(it, expr)
      {
        auto r_it = simplify_rec(*it); // recursive call
        if(r_it.has_changed())
        {
          *it = r_it.expr;
          result=false;
        }
      }
    }
  }

  return result;
}

simplify_exprt::resultt<> simplify_exprt::simplify_node(exprt node)
{
  if(!node.has_operands())
    return unchanged(node); // no change

    // #define DEBUGX

#ifdef DEBUGX
  exprt old(node);
#endif

  exprt expr = node;
  bool no_change_join_operands = join_operands(expr);

  resultt<> r = unchanged(expr);

  if(expr.id()==ID_typecast)
  {
    r = simplify_typecast(to_typecast_expr(expr));
  }
  else if(expr.id()==ID_equal || expr.id()==ID_notequal ||
          expr.id()==ID_gt    || expr.id()==ID_lt ||
          expr.id()==ID_ge    || expr.id()==ID_le)
  {
    r = simplify_inequality(to_binary_relation_expr(expr));
  }
  else if(expr.id()==ID_if)
  {
    r = simplify_if(to_if_expr(expr));
  }
  else if(expr.id()==ID_lambda)
  {
    r = simplify_lambda(to_lambda_expr(expr));
  }
  else if(expr.id()==ID_with)
  {
    r = simplify_with(to_with_expr(expr));
  }
  else if(expr.id()==ID_update)
  {
    r = simplify_update(to_update_expr(expr));
  }
  else if(expr.id()==ID_index)
  {
    r = simplify_index(to_index_expr(expr));
  }
  else if(expr.id()==ID_member)
  {
    r = simplify_member(to_member_expr(expr));
  }
  else if(expr.id()==ID_byte_update_little_endian ||
          expr.id()==ID_byte_update_big_endian)
  {
    r = simplify_byte_update(to_byte_update_expr(expr));
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    r = simplify_byte_extract(to_byte_extract_expr(expr));
  }
  else if(expr.id()==ID_pointer_object)
  {
    r = simplify_pointer_object(to_unary_expr(expr));
  }
  else if(expr.id() == ID_is_dynamic_object)
  {
    r = simplify_is_dynamic_object(to_unary_expr(expr));
  }
  else if(expr.id() == ID_is_invalid_pointer)
  {
    r = simplify_is_invalid_pointer(to_unary_expr(expr));
  }
  else if(expr.id()==ID_object_size)
  {
    r = simplify_object_size(to_unary_expr(expr));
  }
  else if(expr.id()==ID_good_pointer)
  {
    r = simplify_good_pointer(to_unary_expr(expr));
  }
  else if(expr.id()==ID_div)
  {
    r = simplify_div(to_div_expr(expr));
  }
  else if(expr.id()==ID_mod)
  {
    r = simplify_mod(to_mod_expr(expr));
  }
  else if(expr.id()==ID_bitnot)
  {
    r = simplify_bitnot(to_bitnot_expr(expr));
  }
  else if(expr.id()==ID_bitand ||
          expr.id()==ID_bitor ||
          expr.id()==ID_bitxor)
  {
    r = simplify_bitwise(to_multi_ary_expr(expr));
  }
  else if(expr.id()==ID_ashr || expr.id()==ID_lshr || expr.id()==ID_shl)
  {
    r = simplify_shifts(to_shift_expr(expr));
  }
  else if(expr.id()==ID_power)
  {
    r = simplify_power(to_binary_expr(expr));
  }
  else if(expr.id()==ID_plus)
  {
    r = simplify_plus(to_plus_expr(expr));
  }
  else if(expr.id()==ID_minus)
  {
    r = simplify_minus(to_minus_expr(expr));
  }
  else if(expr.id()==ID_mult)
  {
    r = simplify_mult(to_mult_expr(expr));
  }
  else if(expr.id()==ID_floatbv_plus ||
          expr.id()==ID_floatbv_minus ||
          expr.id()==ID_floatbv_mult ||
          expr.id()==ID_floatbv_div)
  {
    r = simplify_floatbv_op(to_ieee_float_op_expr(expr));
  }
  else if(expr.id()==ID_floatbv_typecast)
  {
    r = simplify_floatbv_typecast(to_floatbv_typecast_expr(expr));
  }
  else if(expr.id()==ID_unary_minus)
  {
    r = simplify_unary_minus(to_unary_minus_expr(expr));
  }
  else if(expr.id()==ID_unary_plus)
  {
    r = simplify_unary_plus(to_unary_plus_expr(expr));
  }
  else if(expr.id()==ID_not)
  {
    r = simplify_not(to_not_expr(expr));
  }
  else if(expr.id()==ID_implies ||
          expr.id()==ID_or      || expr.id()==ID_xor ||
          expr.id()==ID_and)
  {
    r = simplify_boolean(expr);
  }
  else if(expr.id()==ID_dereference)
  {
    r = simplify_dereference(to_dereference_expr(expr));
  }
  else if(expr.id()==ID_address_of)
  {
    r = simplify_address_of(to_address_of_expr(expr));
  }
  else if(expr.id()==ID_pointer_offset)
  {
    r = simplify_pointer_offset(to_unary_expr(expr));
  }
  else if(expr.id()==ID_extractbit)
  {
    r = simplify_extractbit(to_extractbit_expr(expr));
  }
  else if(expr.id()==ID_concatenation)
  {
    r = simplify_concatenation(to_concatenation_expr(expr));
  }
  else if(expr.id()==ID_extractbits)
  {
    r = simplify_extractbits(to_extractbits_expr(expr));
  }
  else if(expr.id()==ID_ieee_float_equal ||
          expr.id()==ID_ieee_float_notequal)
  {
    r = simplify_ieee_float_relation(to_binary_relation_expr(expr));
  }
  else if(expr.id() == ID_bswap)
  {
    r = simplify_bswap(to_bswap_expr(expr));
  }
  else if(expr.id()==ID_isinf)
  {
    r = simplify_isinf(to_unary_expr(expr));
  }
  else if(expr.id()==ID_isnan)
  {
    r = simplify_isnan(to_unary_expr(expr));
  }
  else if(expr.id()==ID_isnormal)
  {
    r = simplify_isnormal(to_unary_expr(expr));
  }
  else if(expr.id()==ID_abs)
  {
    r = simplify_abs(to_abs_expr(expr));
  }
  else if(expr.id()==ID_sign)
  {
    r = simplify_sign(to_sign_expr(expr));
  }
  else if(expr.id() == ID_popcount)
  {
    r = simplify_popcount(to_popcount_expr(expr));
  }
  else if(expr.id() == ID_count_leading_zeros)
  {
    r = simplify_clz(to_count_leading_zeros_expr(expr));
  }
  else if(expr.id() == ID_count_trailing_zeros)
  {
    r = simplify_ctz(to_count_trailing_zeros_expr(expr));
  }
  else if(expr.id() == ID_function_application)
  {
    r = simplify_function_application(to_function_application_expr(expr));
  }
  else if(expr.id() == ID_complex_real || expr.id() == ID_complex_imag)
  {
    r = simplify_complex(to_unary_expr(expr));
  }
  else if(
    expr.id() == ID_overflow_plus || expr.id() == ID_overflow_minus ||
    expr.id() == ID_overflow_mult || expr.id() == ID_overflow_shl)
  {
    r = simplify_overflow_binary(to_binary_overflow_expr(expr));
  }
  else if(expr.id() == ID_overflow_unary_minus)
  {
    r = simplify_overflow_unary(to_unary_overflow_expr(expr));
  }
  else if(expr.id() == ID_bitreverse)
  {
    r = simplify_bitreverse(to_bitreverse_expr(expr));
  }

  if(!no_change_join_operands)
    r = changed(r);

#ifdef DEBUGX
  if(
    r.has_changed()
#  ifdef DEBUG_ON_DEMAND
    && debug_on
#  endif
  )
  {
    std::cout << "===== " << node.id() << ": " << format(node) << '\n'
              << " ---> " << format(r.expr) << '\n';
  }
#endif

  return r;
}

simplify_exprt::resultt<> simplify_exprt::simplify_rec(const exprt &expr)
{
  // look up in cache

  #ifdef USE_CACHE
  std::pair<simplify_expr_cachet::containert::iterator, bool>
    cache_result=simplify_expr_cache.container().
      insert(std::pair<exprt, exprt>(expr, exprt()));

  if(!cache_result.second) // found!
  {
    const exprt &new_expr=cache_result.first->second;

    if(new_expr.id().empty())
      return true; // no change

    expr=new_expr;
    return false;
  }
  #endif

  // We work on a copy to prevent unnecessary destruction of sharing.
  exprt tmp=expr;
  bool no_change = simplify_node_preorder(tmp);

  auto simplify_node_result = simplify_node(tmp);

  if(simplify_node_result.has_changed())
  {
    no_change = false;
    tmp = simplify_node_result.expr;
  }

#ifdef USE_LOCAL_REPLACE_MAP
  #if 1
  replace_mapt::const_iterator it=local_replace_map.find(tmp);
  if(it!=local_replace_map.end())
  {
    tmp=it->second;
    no_change = false;
  }
  #else
  if(!local_replace_map.empty() &&
     !replace_expr(local_replace_map, tmp))
  {
    simplify_rec(tmp);
    no_change = false;
  }
  #endif
#endif

  if(no_change) // no change
  {
    return unchanged(expr);
  }
  else // change, new expression is 'tmp'
  {
    POSTCONDITION(as_const(tmp).type() == expr.type());

#ifdef USE_CACHE
    // save in cache
    cache_result.first->second = tmp;
#endif

    return std::move(tmp);
  }
}

/// \return returns true if expression unchanged; returns false if changed
bool simplify_exprt::simplify(exprt &expr)
{
#ifdef DEBUG_ON_DEMAND
  if(debug_on)
    std::cout << "TO-SIMP " << format(expr) << "\n";
#endif
  auto result = simplify_rec(expr);
#ifdef DEBUG_ON_DEMAND
  if(debug_on)
    std::cout << "FULLSIMP " << format(result.expr) << "\n";
#endif
  if(result.has_changed())
  {
    expr = result.expr;
    return false; // change
  }
  else
    return true; // no change
}

/// \return returns true if expression unchanged; returns false if changed
bool simplify(exprt &expr, const namespacet &ns)
{
  return simplify_exprt(ns).simplify(expr);
}

exprt simplify_expr(exprt src, const namespacet &ns)
{
  simplify_exprt(ns).simplify(src);
  return src;
}
