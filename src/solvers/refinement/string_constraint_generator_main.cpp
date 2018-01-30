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

#include <solvers/refinement/string_constraint_generator.h>

#include <limits>
#include <ansi-c/string_constant.h>
#include <java_bytecode/java_types.h>
#include <solvers/refinement/string_refinement_invariant.h>
#include <util/arith_tools.h>
#include <util/pointer_predicates.h>
#include <util/ssa_expr.h>

string_constraint_generatort::string_constraint_generatort(
  const string_constraint_generatort::infot &info,
  const namespacet &ns)
  : max_string_length(info.string_max_length),
    ns(ns)
{
}

const std::vector<exprt> &string_constraint_generatort::get_lemmas() const
{
  return lemmas;
}

const std::vector<string_constraintt> &
string_constraint_generatort::get_constraints() const
{
  return constraints;
}

const std::vector<string_not_contains_constraintt> &
string_constraint_generatort::get_not_contains_constraints() const
{
  return not_contains_constraints;
}

const std::vector<symbol_exprt> &
string_constraint_generatort::get_index_symbols() const
{
  return index_symbols;
}

const std::vector<symbol_exprt> &
string_constraint_generatort::get_boolean_symbols() const
{
  return boolean_symbols;
}

const std::set<array_string_exprt> &
string_constraint_generatort::get_created_strings() const
{
  return created_strings;
}

/// generate constant character expression with character type.
/// \par parameters: integer representing a character, and a type for
///   characters;
/// we do not use char type here because in some languages
/// (for instance java) characters use more than 8 bits.
/// \return constant expression corresponding to the character.
constant_exprt string_constraint_generatort::constant_char(
  int i, const typet &char_type)
{
  return from_integer(i, char_type);
}

/// generate a new symbol expression of the given type with some prefix
/// \par parameters: a prefix and a type
/// \return a symbol of type tp whose name starts with "string_refinement#"
///   followed by prefix
symbol_exprt string_constraint_generatort::fresh_symbol(
  const irep_idt &prefix, const typet &type)
{
  std::ostringstream buf;
  buf << "string_refinement#" << prefix << "#" << ++symbol_count;
  irep_idt name(buf.str());
  return symbol_exprt(name, type);
}

/// generate an index symbol to be used as an universaly quantified variable
/// \par parameters: a prefix
/// \return a symbol of index type whose name starts with the prefix
symbol_exprt string_constraint_generatort::fresh_univ_index(
  const irep_idt &prefix, const typet &type)
{
  return fresh_symbol(prefix, type);
}

/// generate an index symbol which is existentially quantified
/// \par parameters: a prefix
/// \return a symbol of index type whose name starts with the prefix
symbol_exprt string_constraint_generatort::fresh_exist_index(
  const irep_idt &prefix, const typet &type)
{
  symbol_exprt s=fresh_symbol(prefix, type);
  index_symbols.push_back(s);
  return s;
}

/// generate a Boolean symbol which is existentially quantified
/// \par parameters: a prefix
/// \return a symbol of index type whose name starts with the prefix
symbol_exprt string_constraint_generatort::fresh_boolean(
  const irep_idt &prefix)
{
  symbol_exprt b=fresh_symbol(prefix, bool_typet());
  boolean_symbols.push_back(b);
  return b;
}

/// Create a plus expression while adding extra constraints to axioms in order
/// to prevent overflows.
/// \param op1: First term of the sum
/// \param op2: Second term of the sum
/// \return A plus expression representing the sum of the arguments
plus_exprt string_constraint_generatort::plus_exprt_with_overflow_check(
  const exprt &op1, const exprt &op2)
{
  plus_exprt sum(plus_exprt(op1, op2));

  exprt zero=from_integer(0, op1.type());

  binary_relation_exprt neg1(op1, ID_lt, zero);
  binary_relation_exprt neg2(op2, ID_lt, zero);
  binary_relation_exprt neg_sum(sum, ID_lt, zero);

  // We prevent overflows by adding the following constraint:
  // If the signs of the two operands are the same, then the sign of the sum
  // should also be the same.
  implies_exprt no_overflow(equal_exprt(neg1, neg2),
                            equal_exprt(neg1, neg_sum));

  lemmas.push_back(no_overflow);

  return sum;
}

/// Associate an actual finite length to infinite arrays
/// \param s: array expression representing a string
/// \return expression for the length of `s`
exprt string_constraint_generatort::get_length_of_string_array(
  const array_string_exprt &s) const
{
  if(s.length() == infinity_exprt(s.length().type()))
  {
    auto it = length_of_array_.find(s);
    if(it != length_of_array_.end())
      return it->second;
  }
  return s.length();
}

/// construct a string expression whose length and content are new variables
/// \par parameters: a type for string
/// \return a string expression
array_string_exprt string_constraint_generatort::fresh_string(
  const typet &index_type,
  const typet &char_type)
{
  symbol_exprt length = fresh_symbol("string_length", index_type);
  array_typet array_type(char_type, length);
  symbol_exprt content = fresh_symbol("string_content", array_type);
  array_string_exprt str = to_array_string_expr(content);
  created_strings.insert(str);
  add_default_axioms(str);
  return str;
}

// Associate a char array to a char pointer. The size of the char array is a
// variable with no constraint.
array_string_exprt
string_constraint_generatort::associate_char_array_to_char_pointer(
  const exprt &char_pointer,
  const typet &char_array_type)
{
  PRECONDITION(char_pointer.type().id() == ID_pointer);
  PRECONDITION(char_array_type.id() == ID_array);
  PRECONDITION(
    char_array_type.subtype().id() == ID_unsignedbv ||
    char_array_type.subtype().id() == ID_signedbv);
  std::string symbol_name;
  if(
    char_pointer.id() == ID_address_of &&
    (to_address_of_expr(char_pointer).object().id() == ID_index) &&
    char_pointer.op0().op0().id() == ID_array)
  {
    // Do not replace constant arrays
    return to_array_string_expr(
      to_index_expr(to_address_of_expr(char_pointer).object()).array());
  }
  else if(char_pointer.id() == ID_address_of)
  {
    symbol_name = "char_array_of_address";
  }
  else if(char_pointer.id() == ID_if)
  {
    const if_exprt &if_expr = to_if_expr(char_pointer);
    const array_string_exprt t = associate_char_array_to_char_pointer(
      if_expr.true_case(), char_array_type);
    const array_string_exprt f = associate_char_array_to_char_pointer(
      if_expr.false_case(), char_array_type);
    array_typet array_type(
      char_array_type.subtype(),
      if_exprt(
        if_expr.cond(),
        to_array_type(t.type()).size(),
        to_array_type(f.type()).size()));
    return to_array_string_expr(if_exprt(if_expr.cond(), t, f, array_type));
  }
  else if(char_pointer.id() == ID_symbol)
    symbol_name = "char_array_symbol";
  else if(char_pointer.id() == ID_member)
    symbol_name = "char_array_member";
  else if(
    char_pointer.id() == ID_constant &&
    to_constant_expr(char_pointer).get_value() == ID_NULL)
  {
    /// \todo Check if the case char_array_null occurs.
    array_typet array_type(
      char_array_type.subtype(),
      from_integer(0, to_array_type(char_array_type).size().type()));
    symbol_exprt array_sym = fresh_symbol("char_array_null", array_type);
    return to_array_string_expr(array_sym);
  }
  else
    symbol_name = "unknown_char_array";

  array_string_exprt array_sym =
    to_array_string_expr(fresh_symbol(symbol_name, char_array_type));
  auto insert_result =
    arrays_of_pointers_.insert(std::make_pair(char_pointer, array_sym));
  array_string_exprt result = to_array_string_expr(insert_result.first->second);
  add_default_axioms(result);
  return result;
}

/// Associate a char array to a char pointer.
/// Insert in `arrays_of_pointers_` a binding from `ptr` to `arr`.
/// If the length of `arr` is infinite, we create a new integer symbol and add
/// a binding from `arr` to this length in `length_of_array_`.
/// This also adds the default axioms for `arr`.
/// \param f: a function application with argument a character array `arr` and
/// a character pointer `ptr`.
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

  const auto &length = array_expr.length();
  if(length == infinity_exprt(length.type()))
  {
    auto pair = length_of_array_.insert(
      std::make_pair(array_expr, fresh_symbol("string_length", length.type())));
    array_expr.length() = pair.first->second;
  }

  /// \todo We should use a function for inserting the correspondance
  /// between array and pointers.
  const auto it_bool =
    arrays_of_pointers_.insert(std::make_pair(pointer_expr, array_expr));
  INVARIANT(
    it_bool.second, "should not associate two arrays to the same pointer");
  add_default_axioms(to_array_string_expr(array_expr));
  return from_integer(0, f.type());
}

/// Associate an integer length to a char array.
/// This adds an axiom ensuring that `arr.length` and `length` are equal.
/// \param f: a function application with argument a character array `arr` and
/// a integer `length`.
/// \return integer expression equal to 0
exprt string_constraint_generatort::associate_length_to_array(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 2);
  array_string_exprt array_expr = to_array_string_expr(f.arguments()[0]);
  const exprt &new_length = f.arguments()[1];

  const auto &length = get_length_of_string_array(array_expr);
  lemmas.push_back(equal_exprt(length, new_length));
  return from_integer(0, f.type());
}

/// casts an expression to a string expression, or fetches the actual
/// string_exprt in the case of a symbol.
/// \param expr: an expression of refined string type
/// \return a string expression
array_string_exprt
string_constraint_generatort::get_string_expr(const exprt &expr)
{
  PRECONDITION(is_refined_string_type(expr.type()));
  const refined_string_exprt &str = to_string_expr(expr);
  return char_array_of_pointer(str.content(), str.length());
}

/// adds standard axioms about the length of the string and its content: * its
/// length should be positive * it should not exceed max_string_length * if
/// force_printable_characters is true then all characters should belong to the
/// range of ASCII characters between ' ' and '~'
/// \param s: a string expression
/// \return a string expression that is linked to the argument through axioms
///   that are added to the list
void string_constraint_generatort::add_default_axioms(
  const array_string_exprt &s)
{
  // If `s` was already added we do nothing.
  if(!created_strings.insert(s).second)
    return;

  const exprt index_zero = from_integer(0, s.length().type());
  lemmas.push_back(s.axiom_for_length_ge(index_zero));

  if(max_string_length!=std::numeric_limits<size_t>::max())
    lemmas.push_back(s.axiom_for_length_le(max_string_length));
}

/// Add constraint on characters of a string.
///
/// This constraint is
/// \f$ \forall i \in [start, end), low\_char \le s[i] \le high\_char \f$
/// \param s: a string expression
/// \param start: index of the first character to constrain
/// \param end: index at which we stop adding constraints
/// \param char_set: a string of the form "<low_char>-<high_char>" where
///        `<low_char>` and `<high_char>` are two characters, which represents
///        the set of characters that are between `low_char` and `high_char`.
/// \return a string expression that is linked to the argument through axioms
///   that are added to the list
void string_constraint_generatort::add_constraint_on_characters(
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
  const symbol_exprt qvar = fresh_univ_index("char_constr", s.length().type());
  const exprt chr = s[qvar];
  const and_exprt char_in_set(
    binary_relation_exprt(chr, ID_ge, from_integer(low_char, chr.type())),
    binary_relation_exprt(chr, ID_le, from_integer(high_char, chr.type())));
  const string_constraintt sc(qvar, start, end, true_exprt(), char_in_set);
  constraints.push_back(sc);
}

/// Add axioms to ensure all characters of a string belong to a given set.
///
/// The axiom is: \f$\forall i \in [start, end).\ s[i] \in char_set \f$, where
/// `char_set` is given by the string `char_set_string` composed of three
/// characters `low_char`, `-` and `high_char`. Character `c` belongs to
/// `char_set` if \f$low_char \le c \le high_char\f$.
/// \param f: a function application with arguments: integer `|s|`, character
///           pointer `&s[0]`, string `char_set_string`,
///           optional integers `start` and `end`
/// \return integer expression whose value is zero
exprt string_constraint_generatort::add_axioms_for_constrain_characters(
  const function_application_exprt &f)
{
  const auto &args = f.arguments();
  PRECONDITION(3 <= args.size() && args.size() <= 5);
  PRECONDITION(args[2].type().id() == ID_string);
  PRECONDITION(args[2].id() == ID_constant);
  const array_string_exprt s = char_array_of_pointer(args[1], args[0]);
  const irep_idt &char_set_string = to_constant_expr(args[2]).get_value();
  const exprt &start =
    args.size() >= 4 ? args[3] : from_integer(0, s.length().type());
  const exprt &end = args.size() >= 5 ? args[4] : s.length();
  add_constraint_on_characters(s, start, end, char_set_string.c_str());
  return from_integer(0, get_return_code_type());
}

/// Adds creates a new array if it does not already exists
/// \todo This should be replaced by associate_char_array_to_char_pointer
array_string_exprt string_constraint_generatort::char_array_of_pointer(
  const exprt &pointer,
  const exprt &length)
{
  const array_typet array_type(pointer.type().subtype(), length);
  const array_string_exprt array =
    associate_char_array_to_char_pointer(pointer, array_type);
  return array;
}

/// strings contained in this call are converted to objects of type
/// `string_exprt`, through adding axioms. Axioms are then added to enforce that
/// the result corresponds to the function application.
/// \par parameters: an expression containing a function application
/// \return expression corresponding to the result of the function application
exprt string_constraint_generatort::add_axioms_for_function_application(
  const function_application_exprt &expr)
{
  const exprt &name=expr.function();
  PRECONDITION(name.id()==ID_symbol);

  const irep_idt &id=is_ssa_expr(name)?to_ssa_expr(name).get_object_name():
    to_symbol_expr(name).get_identifier();

  exprt res;

  if(id==ID_cprover_char_literal_func)
    res=add_axioms_for_char_literal(expr);
  else if(id==ID_cprover_string_length_func)
    res=add_axioms_for_length(expr);
  else if(id==ID_cprover_string_equal_func)
    res=add_axioms_for_equals(expr);
  else if(id==ID_cprover_string_equals_ignore_case_func)
    res=add_axioms_for_equals_ignore_case(expr);
  else if(id==ID_cprover_string_is_empty_func)
    res=add_axioms_for_is_empty(expr);
  else if(id==ID_cprover_string_char_at_func)
    res=add_axioms_for_char_at(expr);
  else if(id==ID_cprover_string_is_prefix_func)
    res=add_axioms_for_is_prefix(expr);
  else if(id==ID_cprover_string_is_suffix_func)
    res=add_axioms_for_is_suffix(expr);
  else if(id==ID_cprover_string_startswith_func)
    res=add_axioms_for_is_prefix(expr, true);
  else if(id==ID_cprover_string_endswith_func)
    res=add_axioms_for_is_suffix(expr, true);
  else if(id==ID_cprover_string_contains_func)
    res=add_axioms_for_contains(expr);
  else if(id==ID_cprover_string_hash_code_func)
    res=add_axioms_for_hash_code(expr);
  else if(id==ID_cprover_string_index_of_func)
    res=add_axioms_for_index_of(expr);
  else if(id==ID_cprover_string_last_index_of_func)
    res=add_axioms_for_last_index_of(expr);
  else if(id==ID_cprover_string_parse_int_func)
    res=add_axioms_for_parse_int(expr);
  else if(id==ID_cprover_string_code_point_at_func)
    res=add_axioms_for_code_point_at(expr);
  else if(id==ID_cprover_string_code_point_before_func)
    res=add_axioms_for_code_point_before(expr);
  else if(id==ID_cprover_string_code_point_count_func)
    res=add_axioms_for_code_point_count(expr);
  else if(id==ID_cprover_string_offset_by_code_point_func)
    res=add_axioms_for_offset_by_code_point(expr);
  else if(id==ID_cprover_string_compare_to_func)
    res=add_axioms_for_compare_to(expr);
  else if(id==ID_cprover_string_literal_func)
    res=add_axioms_from_literal(expr);
  else if(id==ID_cprover_string_concat_func)
    res=add_axioms_for_concat(expr);
  else if(id==ID_cprover_string_concat_char_func)
    res=add_axioms_for_concat_char(expr);
  else if(id==ID_cprover_string_concat_code_point_func)
    res=add_axioms_for_concat_code_point(expr);
  else if(id==ID_cprover_string_insert_func)
    res=add_axioms_for_insert(expr);
  else if(id==ID_cprover_string_insert_int_func)
    res=add_axioms_for_insert_int(expr);
  else if(id==ID_cprover_string_insert_long_func)
    res = add_axioms_for_insert_int(expr);
  else if(id==ID_cprover_string_insert_bool_func)
    res=add_axioms_for_insert_bool(expr);
  else if(id==ID_cprover_string_insert_char_func)
    res=add_axioms_for_insert_char(expr);
  else if(id==ID_cprover_string_insert_double_func)
    res=add_axioms_for_insert_double(expr);
  else if(id==ID_cprover_string_insert_float_func)
    res=add_axioms_for_insert_float(expr);
  else if(id==ID_cprover_string_substring_func)
    res=add_axioms_for_substring(expr);
  else if(id==ID_cprover_string_trim_func)
    res=add_axioms_for_trim(expr);
  else if(id==ID_cprover_string_to_lower_case_func)
    res=add_axioms_for_to_lower_case(expr);
  else if(id==ID_cprover_string_to_upper_case_func)
    res=add_axioms_for_to_upper_case(expr);
  else if(id==ID_cprover_string_char_set_func)
    res=add_axioms_for_char_set(expr);
  else if(id==ID_cprover_string_empty_string_func)
    res=add_axioms_for_empty_string(expr);
  else if(id==ID_cprover_string_copy_func)
    res=add_axioms_for_copy(expr);
  else if(id==ID_cprover_string_of_int_func)
    res=add_axioms_from_int(expr);
  else if(id==ID_cprover_string_of_int_hex_func)
    res=add_axioms_from_int_hex(expr);
  else if(id==ID_cprover_string_of_float_func)
    res=add_axioms_for_string_of_float(expr);
  else if(id==ID_cprover_string_of_float_scientific_notation_func)
    res=add_axioms_from_float_scientific_notation(expr);
  else if(id==ID_cprover_string_of_double_func)
    res=add_axioms_from_double(expr);
  else if(id==ID_cprover_string_of_long_func)
    res=add_axioms_from_long(expr);
  else if(id==ID_cprover_string_of_bool_func)
    res=add_axioms_from_bool(expr);
  else if(id==ID_cprover_string_of_char_func)
    res=add_axioms_from_char(expr);
  else if(id==ID_cprover_string_set_length_func)
    res=add_axioms_for_set_length(expr);
  else if(id==ID_cprover_string_delete_func)
    res=add_axioms_for_delete(expr);
  else if(id==ID_cprover_string_delete_char_at_func)
    res=add_axioms_for_delete_char_at(expr);
  else if(id==ID_cprover_string_replace_func)
    res=add_axioms_for_replace(expr);
  else if(id==ID_cprover_string_intern_func)
    res=add_axioms_for_intern(expr);
  else if(id==ID_cprover_string_format_func)
    res=add_axioms_for_format(expr);
  else if(id == ID_cprover_associate_array_to_pointer_func)
    res = associate_array_to_pointer(expr);
  else if(id == ID_cprover_associate_length_to_array_func)
    res = associate_length_to_array(expr);
  else if(id == ID_cprover_string_constrain_characters_func)
    res = add_axioms_for_constrain_characters(expr);
  else
  {
    std::string msg(
      "string_constraint_generator::function_application: unknown symbol :");
    msg+=id2string(id);
    DATA_INVARIANT(false, string_refinement_invariantt(msg));
  }
  return res;
}

/// add axioms to say that the returned string expression is equal to the
/// argument of the function application
/// \deprecated should use substring instead
/// \param f: function application with one argument, which is a string,
/// or three arguments: string, integer offset and count
/// \return a new string expression
exprt string_constraint_generatort::add_axioms_for_copy(
  const function_application_exprt &f)
{
  const auto &args=f.arguments();
  PRECONDITION(args.size() == 3 || args.size() == 5);
  const array_string_exprt res = char_array_of_pointer(args[1], args[0]);
  const array_string_exprt str = get_string_expr(args[2]);
  const typet &index_type = str.length().type();
  const exprt offset = args.size() == 3 ? from_integer(0, index_type) : args[3];
  const exprt count = args.size() == 3 ? str.length() : args[4];
  return add_axioms_for_substring(res, str, offset, plus_exprt(offset, count));
}

/// Length of a string
///
/// Returns the length of the string argument of the given function application
/// \param f: function application with argument string `str`
/// \return expression `|str|`
exprt string_constraint_generatort::add_axioms_for_length(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 1);
  const array_string_exprt str = get_string_expr(f.arguments()[0]);
  return str.length();
}

/// expression true exactly when the index is positive
/// \param x: an index expression
/// \return a Boolean expression
exprt string_constraint_generatort::axiom_for_is_positive_index(const exprt &x)
{
  return binary_relation_exprt(x, ID_ge, from_integer(0, x.type()));
}

/// add axioms stating that the returned value is equal to the argument
/// \param f: function application with one character argument
/// \return a new character expression
exprt string_constraint_generatort::add_axioms_for_char_literal(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  PRECONDITION(args.size()==1); // there should be exactly 1 arg to char literal

  const exprt &arg=args[0];
  // for C programs argument to char literal should be one string constant
  // of size 1.
  if(arg.operands().size()==1 &&
     arg.op0().operands().size()==1 &&
     arg.op0().op0().operands().size()==2 &&
     arg.op0().op0().op0().id()==ID_string_constant)
  {
    const string_constantt s=to_string_constant(arg.op0().op0().op0());
    irep_idt sval=s.get_value();
    CHECK_RETURN(sval.size()==1);
    return from_integer(unsigned(sval[0]), arg.type());
  }
  else
  {
    // convert_char_literal unimplemented
    UNIMPLEMENTED;
    // For the compiler
    throw 0;
  }
}

/// Character at a given position
///
/// Add axioms stating that the character of the string at position given by
/// second argument is equal to the returned value.
/// This axiom is \f$ char = str[i] \f$.
/// \param f: function application with arguments string `str` and integer `i`
/// \return character expression `char`
exprt string_constraint_generatort::add_axioms_for_char_at(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 2);
  array_string_exprt str = get_string_expr(f.arguments()[0]);
  symbol_exprt char_sym = fresh_symbol("char", str.type().subtype());
  lemmas.push_back(equal_exprt(char_sym, str[f.arguments()[1]]));
  return char_sym;
}
