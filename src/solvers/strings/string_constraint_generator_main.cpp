/*******************************************************************\

Module: Generates string constraints to link results from string functions
        with their arguments. This is inspired by the PASS paper at HVC'13:
        "PASS: String Solving with Parameterized Array and Interval Automaton"
        by Guodong Li and Indradeep Ghosh, which gives examples of constraints
        for several functions.

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints to link results from string functions with
///   their arguments. This is inspired by the PASS paper at HVC'13: "PASS:
///   String Solving with Parameterized Array and Interval Automaton" by Guodong
///   Li and Indradeep Ghosh, which gives examples of constraints for several
///   functions.

#include "string_constraint_generator.h"
#include "string_refinement_invariant.h"

#include <iterator>
#include <limits>

#include <util/arith_tools.h>
#include <util/deprecate.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>
#include <util/ssa_expr.h>
#include <util/string_constant.h>

string_constraint_generatort::string_constraint_generatort(const namespacet &ns)
  : array_pool(fresh_symbol), ns(ns)
{
}

exprt sum_overflows(const plus_exprt &sum)
{
  PRECONDITION(sum.operands().size() == 2);
  const exprt zero = from_integer(0, sum.op0().type());
  const binary_relation_exprt op0_negative(sum.op0(), ID_lt, zero);
  const binary_relation_exprt op1_negative(sum.op1(), ID_lt, zero);
  const binary_relation_exprt sum_negative(sum, ID_lt, zero);

  // overflow happens when we add two values of same sign but their sum has a
  // different sign
  return and_exprt(
    equal_exprt(op0_negative, op1_negative),
    notequal_exprt(op1_negative, sum_negative));
}

/// Associate a char array to a char pointer.
/// Insert in `array_pool` a binding from `ptr` to `arr`. If the length of `arr`
/// is infinite, a new integer symbol is created and stored in `array_pool`.
/// This also adds the default axioms for `arr`.
/// \param f: a function application with argument a character array `arr` and
///   a character pointer `ptr`.
exprt string_constraint_generatort::associate_array_to_pointer(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 2);

  /// \todo: we allow expression of the form of `arr[0]` instead of `arr` as
  ///        the array argument but this could go away.
  array_string_exprt array_expr = to_array_string_expr(
    f.arguments()[0].id() == ID_index ? to_index_expr(f.arguments()[0]).array()
                                      : f.arguments()[0]);

  const exprt &pointer_expr = f.arguments()[1];
  array_pool.insert(simplify_expr(pointer_expr, ns), array_expr);
  // created_strings.emplace(to_array_string_expr(array_expr));
  return from_integer(0, f.type());
}

/// Associate an integer length to a char array.
/// This adds an axiom ensuring that `arr.length` and `length` are equal.
/// \param f: a function application with argument a character array `arr` and
///   an integer `length`.
/// \return integer expression equal to 0
exprt string_constraint_generatort::associate_length_to_array(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 2);
  array_string_exprt array_expr = to_array_string_expr(f.arguments()[0]);
  const exprt &new_length = f.arguments()[1];

  const auto &length = array_pool.get_length(array_expr);
  constraints.existential.push_back(equal_exprt(length, new_length));
  return from_integer(0, f.type());
}

void string_constraintst::clear()
{
  existential.clear();
  universal.clear();
  not_contains.clear();
}

/// Merge two sets of constraints by appending to the first one
void merge(string_constraintst &result, string_constraintst other)
{
  std::move(
    other.existential.begin(),
    other.existential.end(),
    std::back_inserter(result.existential));
  std::move(
    other.universal.begin(),
    other.universal.end(),
    std::back_inserter(result.universal));
  std::move(
    other.not_contains.begin(),
    other.not_contains.end(),
    std::back_inserter(result.not_contains));
}

/// Add constraint on characters of a string.
///
/// This constraint is
/// \f$ \forall i \in [start, end), low\_char \le s[i] \le high\_char \f$
/// \param fresh_symbol: generator of fresh symbols
/// \param s: a string expression
/// \param start: index of the first character to constrain
/// \param end: index at which we stop adding constraints
/// \param char_set: a string of the form "<low_char>-<high_char>" where
///   `<low_char>` and `<high_char>` are two characters, which represents the
///   set of characters that are between `low_char` and `high_char`.
/// \return a string expression that is linked to the argument through axioms
///   that are added to the list
string_constraintst add_constraint_on_characters(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &s,
  const exprt &start,
  const exprt &end,
  const std::string &char_set)
{
  // Parse char_set
  PRECONDITION(char_set.length() == 3);
  PRECONDITION(char_set[1] == '-');
  const char &low_char = char_set[0];
  const char &high_char = char_set[2];

  // Add constraint
  const symbol_exprt qvar = fresh_symbol("char_constr", s.length_type());
  const exprt chr = s[qvar];
  const and_exprt char_in_set(
    binary_relation_exprt(chr, ID_ge, from_integer(low_char, chr.type())),
    binary_relation_exprt(chr, ID_le, from_integer(high_char, chr.type())));
  const string_constraintt sc(
    qvar, zero_if_negative(start), zero_if_negative(end), char_in_set);
  return {{}, {sc}, {}};
}

/// Add axioms to ensure all characters of a string belong to a given set.
///
/// The axiom is: \f$\forall i \in [start, end).\ s[i] \in char_set \f$, where
/// `char_set` is given by the string `char_set_string` composed of three
/// characters `low_char`, `-` and `high_char`. Character `c` belongs to
/// `char_set` if \f$low_char \le c \le high_char\f$.
/// \param fresh_symbol: generator of fresh symbols
/// \param f: a function application with arguments: integer `|s|`, character
///   pointer `&s[0]`, string `char_set_string`, optional integers `start` and
///   `end`
/// \param array_pool: pool of arrays representing strings
/// \return integer expression whose value is zero
std::pair<exprt, string_constraintst> add_axioms_for_constrain_characters(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  const auto &args = f.arguments();
  PRECONDITION(3 <= args.size() && args.size() <= 5);
  PRECONDITION(args[2].type().id() == ID_string);
  PRECONDITION(args[2].id() == ID_constant);

  const array_string_exprt s = array_pool.find(args[1], args[0]);
  const irep_idt &char_set_string = to_constant_expr(args[2]).get_value();
  const exprt &start =
    args.size() >= 4 ? args[3] : from_integer(0, s.length_type());
  const exprt &end = args.size() >= 5 ? args[4] : s.length();
  auto constraints = add_constraint_on_characters(
    fresh_symbol, s, start, end, char_set_string.c_str());
  return {from_integer(0, get_return_code_type()), std::move(constraints)};
}

signedbv_typet get_return_code_type()
{
  return signedbv_typet(32);
}

static irep_idt get_function_name(const function_application_exprt &expr)
{
  const exprt &name = expr.function();
  PRECONDITION(name.id() == ID_symbol);
  PRECONDITION(!is_ssa_expr(name));
  return to_symbol_expr(name).get_identifier();
}

optionalt<exprt> string_constraint_generatort::make_array_pointer_association(
  const function_application_exprt &expr)
{
  const irep_idt &id = get_function_name(expr);
  if(id == ID_cprover_associate_array_to_pointer_func)
    return associate_array_to_pointer(expr);
  else if(id == ID_cprover_associate_length_to_array_func)
    return associate_length_to_array(expr);
  return {};
}

/// strings contained in this call are converted to objects of type
/// `string_exprt`, through adding axioms. Axioms are then added to enforce that
/// the result corresponds to the function application.
/// \param expr: an expression containing a function application
/// \return expression corresponding to the result of the function application
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_function_application(
  const function_application_exprt &expr)
{
  const irep_idt &id = get_function_name(expr);

  if(id == ID_cprover_char_literal_func)
    return add_axioms_for_char_literal(expr);
  else if(id == ID_cprover_string_length_func)
    return add_axioms_for_length(expr, array_pool);
  else if(id == ID_cprover_string_equal_func)
    return add_axioms_for_equals(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_equals_ignore_case_func)
    return add_axioms_for_equals_ignore_case(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_is_empty_func)
    return add_axioms_for_is_empty(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_char_at_func)
    return add_axioms_for_char_at(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_is_prefix_func)
    return add_axioms_for_is_prefix(fresh_symbol, expr, false, array_pool);
  else if(id == ID_cprover_string_is_suffix_func)
    return add_axioms_for_is_suffix(fresh_symbol, expr, false, array_pool);
  else if(id == ID_cprover_string_startswith_func)
    return add_axioms_for_is_prefix(fresh_symbol, expr, true, array_pool);
  else if(id == ID_cprover_string_endswith_func)
    return add_axioms_for_is_suffix(fresh_symbol, expr, true, array_pool);
  else if(id == ID_cprover_string_contains_func)
    return add_axioms_for_contains(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_index_of_func)
    return add_axioms_for_index_of(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_last_index_of_func)
    return add_axioms_for_last_index_of(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_parse_int_func)
    return add_axioms_for_parse_int(fresh_symbol, expr, array_pool, ns);
  else if(id == ID_cprover_string_code_point_at_func)
    return add_axioms_for_code_point_at(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_code_point_before_func)
    return add_axioms_for_code_point_before(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_code_point_count_func)
    return add_axioms_for_code_point_count(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_offset_by_code_point_func)
    return add_axioms_for_offset_by_code_point(fresh_symbol, expr);
  else if(id == ID_cprover_string_compare_to_func)
    return add_axioms_for_compare_to(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_literal_func)
    return add_axioms_from_literal(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_concat_code_point_func)
    return add_axioms_for_concat_code_point(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_insert_func)
    return add_axioms_for_insert(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_insert_int_func)
    return add_axioms_for_insert_int(fresh_symbol, expr, array_pool, ns);
  else if(id == ID_cprover_string_insert_long_func)
    return add_axioms_for_insert_int(fresh_symbol, expr, array_pool, ns);
  else if(id == ID_cprover_string_insert_bool_func)
    return add_axioms_for_insert_bool(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_insert_char_func)
    return add_axioms_for_insert_char(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_insert_double_func)
    return add_axioms_for_insert_double(fresh_symbol, expr, array_pool, ns);
  else if(id == ID_cprover_string_insert_float_func)
    return add_axioms_for_insert_float(fresh_symbol, expr, array_pool, ns);
  else if(id == ID_cprover_string_substring_func)
    return add_axioms_for_substring(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_trim_func)
    return add_axioms_for_trim(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_empty_string_func)
    return add_axioms_for_empty_string(expr);
  else if(id == ID_cprover_string_copy_func)
    return add_axioms_for_copy(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_of_int_hex_func)
    return add_axioms_from_int_hex(expr, array_pool);
  else if(id == ID_cprover_string_of_float_func)
    return add_axioms_for_string_of_float(fresh_symbol, expr, array_pool, ns);
  else if(id == ID_cprover_string_of_float_scientific_notation_func)
    return add_axioms_from_float_scientific_notation(
      fresh_symbol, expr, array_pool, ns);
  else if(id == ID_cprover_string_of_double_func)
    return add_axioms_from_double(fresh_symbol, expr, array_pool, ns);
  else if(id == ID_cprover_string_of_long_func)
    return add_axioms_from_long(expr, array_pool, ns);
  else if(id == ID_cprover_string_of_bool_func)
    return add_axioms_from_bool(expr, array_pool);
  else if(id == ID_cprover_string_of_char_func)
    return add_axioms_from_char(expr, array_pool);
  else if(id == ID_cprover_string_set_length_func)
    return add_axioms_for_set_length(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_delete_func)
    return add_axioms_for_delete(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_delete_char_at_func)
    return add_axioms_for_delete_char_at(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_replace_func)
    return add_axioms_for_replace(fresh_symbol, expr, array_pool);
  else if(id == ID_cprover_string_format_func)
    return add_axioms_for_format(fresh_symbol, expr, array_pool, message, ns);
  else if(id == ID_cprover_string_constrain_characters_func)
    return add_axioms_for_constrain_characters(fresh_symbol, expr, array_pool);
  else
  {
    std::string msg(
      "string_constraint_generator::function_application: unknown symbol :");
    msg += id2string(id);
    DATA_INVARIANT(false, string_refinement_invariantt(msg));
  }
  UNREACHABLE;
}

/// add axioms to say that the returned string expression is equal to the
/// argument of the function application
/// \deprecated should use substring instead
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with one argument, which is a string,
///   or three arguments: string, integer offset and count
/// \param array_pool: pool of arrays representing strings
/// \return a new string expression
DEPRECATED(SINCE(2017, 10, 5, "should use substring instead"))
std::pair<exprt, string_constraintst> add_axioms_for_copy(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  const auto &args = f.arguments();
  PRECONDITION(args.size() == 3 || args.size() == 5);
  const array_string_exprt res = array_pool.find(args[1], args[0]);
  const array_string_exprt str = get_string_expr(array_pool, args[2]);
  const typet &index_type = str.length_type();
  const exprt offset = args.size() == 3 ? from_integer(0, index_type) : args[3];
  const exprt count = args.size() == 3 ? str.length() : args[4];
  return add_axioms_for_substring(
    fresh_symbol, res, str, offset, plus_exprt(offset, count));
}

/// Length of a string
///
/// Returns the length of the string argument of the given function application
/// \param f: function application with argument string `str`
/// \param array_pool: pool of arrays representing strings
/// \return expression `|str|`
std::pair<exprt, string_constraintst> add_axioms_for_length(
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  PRECONDITION(f.arguments().size() == 1);
  const array_string_exprt str = get_string_expr(array_pool, f.arguments()[0]);
  return {str.length(), {}};
}

/// \param x: an expression
/// \return a Boolean expression true exactly when `x` is positive
exprt is_positive(const exprt &x)
{
  return binary_relation_exprt(x, ID_ge, from_integer(0, x.type()));
}

/// add axioms stating that the returned value is equal to the argument
/// \param f: function application with one character argument
/// \return a new character expression
std::pair<exprt, string_constraintst>
add_axioms_for_char_literal(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  PRECONDITION(
    args.size() == 1); // there should be exactly 1 arg to char literal

  const exprt &arg = args[0];
  // for C programs argument to char literal should be one string constant
  // of size 1.
  if(
    arg.operands().size() == 1 && arg.op0().operands().size() == 1 &&
    arg.op0().op0().operands().size() == 2 &&
    arg.op0().op0().op0().id() == ID_string_constant)
  {
    const string_constantt &s = to_string_constant(arg.op0().op0().op0());
    const std::string &sval = id2string(s.get_value());
    CHECK_RETURN(sval.size() == 1);
    return {from_integer(unsigned(sval[0]), arg.type()), {}};
  }
  else
  {
    UNIMPLEMENTED;
  }
}

/// Character at a given position
///
/// Add axioms stating that the character of the string at position given by
/// second argument is equal to the returned value.
/// This axiom is \f$ char = str[i] \f$.
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with arguments string `str` and integer `i`
/// \param array_pool: pool of arrays representing strings
/// \return character expression `char`
std::pair<exprt, string_constraintst> add_axioms_for_char_at(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  PRECONDITION(f.arguments().size() == 2);
  array_string_exprt str = get_string_expr(array_pool, f.arguments()[0]);
  symbol_exprt char_sym = fresh_symbol("char", str.type().subtype());
  string_constraintst constraints;
  constraints.existential = {equal_exprt(char_sym, str[f.arguments()[1]])};
  return {std::move(char_sym), std::move(constraints)};
}

exprt minimum(const exprt &a, const exprt &b)
{
  return if_exprt(binary_relation_exprt(a, ID_le, b), a, b);
}

exprt maximum(const exprt &a, const exprt &b)
{
  return if_exprt(binary_relation_exprt(a, ID_le, b), b, a);
}

/// Returns a non-negative version of the argument.
/// \param expr: expression of which we want a non-negative version
/// \return `max(0, expr)`
exprt zero_if_negative(const exprt &expr)
{
  return maximum(from_integer(0, expr.type()), expr);
}

/// Combine the results of two `add_axioms` function by taking the maximum of
/// the return codes and merging the constraints.
std::pair<exprt, string_constraintst> combine_results(
  std::pair<exprt, string_constraintst> result1,
  std::pair<exprt, string_constraintst> result2)
{
  const exprt return_code = maximum(result1.first, result2.first);
  merge(result2.second, std::move(result1.second));
  return {return_code, std::move(result2.second)};
}
