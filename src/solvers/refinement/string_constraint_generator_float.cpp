/*******************************************************************\

Module: Generates string constraints for functions generating strings
        from other types, in particular int, long, float, double, char, bool

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for functions generating strings from other
/// types, in particular int, long, float, double, char, bool

#include <solvers/floatbv/float_bv.h>

#include "string_constraint_generator.h"


/// Gets the unbiased exponent in a floating-point bit-vector
///
/// \todo Refactor with float_bv.cpp float_utils.h
/// \param src: a floating point expression
/// \param spec: specification for floating points
/// \return A new 32 bit integer expression representing the exponent.
///   Note that 32 bits are sufficient for the exponent even
///   in octuple precision.
exprt get_exponent(
  const exprt &src, const ieee_float_spect &spec)
{
  const extractbits_exprt exp_bits(
    src, spec.f + spec.e - 1, spec.f, unsignedbv_typet(spec.e));

  // Exponent is in biased form (numbers from -128 to 127 are encoded with
  // integer from 0 to 255) we have to remove the bias.
  return minus_exprt(
    typecast_exprt(exp_bits, signedbv_typet(32)),
    from_integer(spec.bias(), signedbv_typet(32)));
}

/// Gets the fraction without hidden bit
/// \param src: a floating point expression
/// \param spec: specification for floating points
/// \return An unsigned value representing the fractional part.
exprt get_fraction(const exprt &src, const ieee_float_spect &spec)
{
  return extractbits_exprt(src, spec.f-1, 0, unsignedbv_typet(spec.f));
}

/// Gets the significand as a java integer, looking for the hidden bit.
/// Since the most significant bit is 1 for normalized number, it is not part
/// of the encoding of the significand and is 0 only if all the bits of the
/// exponent are 0, that is why it is called the hidden bit.
/// \param src: a floating point expression
/// \param spec: specification for floating points
/// \param type: type of the output, should be unsigned with width greater than
///   the width of the significand in the given spec
/// \return An integer expression of the given type representing the
///   significand.
exprt get_significand(
  const exprt &src, const ieee_float_spect &spec, const typet &type)
{
  PRECONDITION(type.id()==ID_unsignedbv);
  PRECONDITION(to_unsignedbv_type(type).get_width()>spec.f);
  typecast_exprt fraction(get_fraction(src, spec), type);
  exprt exponent=get_exponent(src, spec);
  equal_exprt all_zeros(exponent, from_integer(0, exponent.type()));
  exprt hidden_bit=from_integer((1 << spec.f), type);
  bitor_exprt with_hidden_bit(fraction, hidden_bit);
  return if_exprt(all_zeros, fraction, with_hidden_bit);
}

/// Create an expression to represent a float or double value.
/// \param f: a floating point value in double precision
/// \param float_spec: a specification for floats
/// \return an expression representing this floating point
exprt constant_float(const double f, const ieee_float_spect &float_spec)
{
  ieee_floatt fl(float_spec);
  if(float_spec==ieee_float_spect::single_precision())
    fl.from_float(f);
  else if(float_spec==ieee_float_spect::double_precision())
    fl.from_double(f);
  else
    UNREACHABLE;
  return fl.to_expr();
}

/// Round a float expression to an integer closer to 0
/// \param f: expression representing a float
/// \return expression representing a 32 bit integer
exprt round_expr_to_zero(const exprt &f)
{
  exprt rounding=from_integer(ieee_floatt::ROUND_TO_ZERO, unsignedbv_typet(32));
  return floatbv_typecast_exprt(f, rounding, signedbv_typet(32));
}

/// Multiplication of expressions representing floating points.
/// Note that the rounding mode is set to ROUND_TO_EVEN.
/// \param f: a floating point expression
/// \param g: a floating point expression
/// \return An expression representing floating point multiplication.
exprt floatbv_mult(const exprt &f, const exprt &g)
{
  PRECONDITION(f.type()==g.type());
  ieee_floatt::rounding_modet rounding=ieee_floatt::ROUND_TO_EVEN;
  exprt mult(ID_floatbv_mult, f.type());
  mult.copy_to_operands(f);
  mult.copy_to_operands(g);
  mult.copy_to_operands(from_integer(rounding, unsignedbv_typet(32)));
  return mult;
}

/// Convert integers to floating point to be used in operations with
/// other values that are in floating point representation.
/// \param i: an expression representing an integer
/// \param spec: specification for floating point numbers
/// \return An expression representing the value of the input
///   integer as a float.
exprt floatbv_of_int_expr(const exprt &i, const ieee_float_spect &spec)
{
  exprt rounding=from_integer(ieee_floatt::ROUND_TO_ZERO, unsignedbv_typet(32));
  return floatbv_typecast_exprt(i, rounding, spec.to_type());
}

/// Estimate the decimal exponent that should be used to represent a given
/// floating point value in decimal.
/// We are looking for \f$d\f$ such that \f$n * 10^d = m * 2^e\f$, so:
/// \f$d = log_10(m) + log_10(2) * e - log_10(n)\f$
/// m -- the fraction -- should be between 1 and 2 so log_10(m)
/// in [0,log_10(2)].
/// n -- the fraction in base 10 -- should be between 1 and 10 so
/// log_10(n) in [0, 1].
/// So the estimate is given by:
/// d ~=~  floor(log_10(2) * e)
/// \param f: a floating point expression
/// \param spec: specification for floating point
exprt estimate_decimal_exponent(const exprt &f, const ieee_float_spect &spec)
{
  exprt log_10_of_2=constant_float(0.30102999566398119521373889472449302, spec);
  exprt bin_exp=get_exponent(f, spec);
  exprt float_bin_exp=floatbv_of_int_expr(bin_exp, spec);
  exprt dec_exp=floatbv_mult(float_bin_exp, log_10_of_2);
  binary_relation_exprt negative_exp(dec_exp, ID_lt, constant_float(0.0, spec));
  // Rounding to zero is not correct for negative numbers, so we substract 1.
  minus_exprt dec_minus_one(dec_exp, constant_float(1.0, spec));
  if_exprt adjust_for_neg(negative_exp, dec_minus_one, dec_exp);
  return round_expr_to_zero(adjust_for_neg);
}

/// String representation of a float value
///
/// Add axioms corresponding to the String.valueOf(F) java function
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with one float argument
/// \param array_pool: pool of arrays representing strings
/// \param ns: namespace
/// \return an integer expression
std::pair<exprt, string_constraintst> add_axioms_for_string_of_float(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool,
  const namespacet &ns)
{
  PRECONDITION(f.arguments().size() == 3);
  array_string_exprt res =
    char_array_of_pointer(array_pool, f.arguments()[1], f.arguments()[0]);
  return add_axioms_for_string_of_float(
    fresh_symbol, res, f.arguments()[2], array_pool, ns);
}

/// Add axioms corresponding to the String.valueOf(D) java function
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with one double argument
/// \param array_pool: pool of arrays representing strings
/// \param ns: namespace
/// \return an integer expression
std::pair<exprt, string_constraintst> add_axioms_from_double(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool,
  const namespacet &ns)
{
  return add_axioms_for_string_of_float(fresh_symbol, f, array_pool, ns);
}

/// Add axioms corresponding to the integer part of m, in decimal form with no
/// leading zeroes, followed by &apos;.&apos;, followed by
/// one or more decimal digits representing the fractional part of m.
/// This specification is correct for inputs that do not exceed 100000 and the
/// function is unspecified for other values.
///
/// \todo This specification is not correct for negative numbers and
/// double precision.
/// \param fresh_symbol: generator of fresh symbols
/// \param res: string expression corresponding to the result
/// \param f: a float expression, which is positive
/// \param array_pool: pool of arrays representing strings
/// \param ns: namespace
/// \return an integer expression, different from zero if an error should be
///   raised
std::pair<exprt, string_constraintst> add_axioms_for_string_of_float(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const exprt &f,
  array_poolt &array_pool,
  const namespacet &ns)
{
  const floatbv_typet &type=to_floatbv_type(f.type());
  const ieee_float_spect float_spec(type);
  const typet &char_type = res.content().type().subtype();
  const typet &index_type = res.length().type();

  // We will look at the first 5 digits of the fractional part.
  // shifted is floor(f * 1e5)
  const exprt shifting = constant_float(1e5, float_spec);
  const exprt shifted = round_expr_to_zero(floatbv_mult(f, shifting));
  // Numbers with greater or equal value to the following, should use
  // the exponent notation.
  const exprt max_non_exponent_notation = from_integer(100000, shifted.type());
  // fractional_part is floor(f * 100000) % 100000
  const mod_exprt fractional_part(shifted, max_non_exponent_notation);
  const array_string_exprt fractional_part_str =
    array_pool.fresh_string(index_type, char_type);
  auto result1 = add_axioms_for_fractional_part(
    fresh_symbol, fractional_part_str, fractional_part, 6);

  // The axiom added to convert to integer should always be satisfiable even
  // when the preconditions are not satisfied.
  const mod_exprt integer_part(
    round_expr_to_zero(f), max_non_exponent_notation);
  // We should not need more than 8 characters to represent the integer
  // part of the float.
  const array_string_exprt integer_part_str =
    array_pool.fresh_string(index_type, char_type);
  auto result2 = add_axioms_for_string_of_int(
    fresh_symbol, integer_part_str, integer_part, 8, ns);

  auto result3 = add_axioms_for_concat(
    fresh_symbol, res, integer_part_str, fractional_part_str);
  merge(result3.second, std::move(result1.second));
  merge(result3.second, std::move(result2.second));

  const auto return_code =
    maximum(result1.first, maximum(result2.first, result3.first));
  return {return_code, std::move(result3.second)};
}

/// Add axioms for representing the fractional part of a floating point starting
/// with a dot
/// \param fresh_symbol: generator of fresh symbols
/// \param res: string expression for the result
/// \param int_expr: an integer expression
/// \param max_size: a maximal size for the string, this includes the
///   potential minus sign and therefore should be greater than 2
/// \return code 0 on success
std::pair<exprt, string_constraintst> add_axioms_for_fractional_part(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const exprt &int_expr,
  size_t max_size)
{
  PRECONDITION(int_expr.type().id()==ID_signedbv);
  PRECONDITION(max_size>=2);
  string_constraintst constraints;
  const typet &type=int_expr.type();
  const typet &char_type = res.content().type().subtype();
  const typet &index_type = res.length().type();
  const exprt ten = from_integer(10, type);
  const exprt zero_char = from_integer('0', char_type);
  const exprt nine_char = from_integer('9', char_type);
  const exprt max = from_integer(max_size, index_type);

  // We add axioms:
  // a1 : 2 <= |res| <= max_size
  // a2 : starts_with_dot && no_trailing_zero && is_number
  // starts_with_dot: res[0] = '.'
  // is_number: forall i:[1, max_size[. '0' < res[i] < '9'
  // no_trailing_zero: forall j:[2, max_size[. !(|res| = j+1 && res[j] = '0')
  // a3 : int_expr = sum_j 10^j (j < |res| ? res[j] - '0' : 0)

  const and_exprt a1(
    axiom_for_length_gt(res, 1), axiom_for_length_le(res, max));
  constraints.existential.push_back(a1);

  equal_exprt starts_with_dot(res[0], from_integer('.', char_type));

  exprt::operandst digit_constraints;
  digit_constraints.push_back(starts_with_dot);
  exprt sum=from_integer(0, type);

  for(size_t j=1; j<max_size; j++)
  {
    // after_end is |res| <= j
    binary_relation_exprt after_end(
      res.length(), ID_le, from_integer(j, res.length().type()));
    mult_exprt ten_sum(sum, ten);

    // sum = 10 * sum + after_end ? 0 : (res[j]-'0')
    if_exprt to_add(
      after_end,
      from_integer(0, type),
      typecast_exprt(minus_exprt(res[j], zero_char), type));
    sum=plus_exprt(ten_sum, to_add);

    and_exprt is_number(
      binary_relation_exprt(res[j], ID_ge, zero_char),
      binary_relation_exprt(res[j], ID_le, nine_char));
    digit_constraints.push_back(is_number);

    // There are no trailing zeros except for ".0" (i.e j=2)
    if(j>1)
    {
      not_exprt no_trailing_zero(and_exprt(
        equal_exprt(res.length(), from_integer(j+1, res.length().type())),
      equal_exprt(res[j], zero_char)));
      digit_constraints.push_back(no_trailing_zero);
    }
  }

  exprt a2=conjunction(digit_constraints);
  constraints.existential.push_back(a2);

  equal_exprt a3(int_expr, sum);
  constraints.existential.push_back(a3);

  return {from_integer(0, signedbv_typet(32)), std::move(constraints)};
}

/// Add axioms to write the float in scientific notation.
///
/// A float is represented as \f$f = m * 2^e\f$ where \f$0 <= m < 2\f$ is the
/// significand and \f$-126 <= e <= 127\f$ is the exponent.
/// We want an alternate representation by finding \f$n\f$ and
/// \f$d\f$ such that \f$f=n*10^d\f$. We can estimate \f$d\f$ the following way:
/// \f$d ~= log_10(f/n) ~= log_10(m) + log_10(2) * e - log_10(n)\f$
/// \f$d = floor(log_10(2) * e)\f$
/// Then \f$n\f$ can be expressed by the equation:
/// \f$log_10(n) = log_10(m) + log_10(2) * e - d\f$
/// \f$n = f / 10^d = m * 2^e / 10^d = m * 2^e / 10^(floor(log_10(2) * e))\f$
/// \todo For now we only consider single precision.
/// \param fresh_symbol: generator of fresh symbols
/// \param res: string expression representing the float in scientific notation
/// \param f: a float expression, which is positive
/// \param array_pool: pool of arrays representing strings
/// \param ns: namespace
/// \return a integer expression different from 0 to signal an exception
std::pair<exprt, string_constraintst> add_axioms_from_float_scientific_notation(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const exprt &f,
  array_poolt &array_pool,
  const namespacet &ns)
{
  string_constraintst constraints;
  const ieee_float_spect float_spec = ieee_float_spect::single_precision();
  const typet float_type = float_spec.to_type();
  const signedbv_typet int_type(32);
  const typet &index_type = res.length().type();
  const typet &char_type = res.content().type().subtype();

  // This is used for rounding float to integers.
  exprt round_to_zero_expr=from_integer(ieee_floatt::ROUND_TO_ZERO, int_type);

  // `bin_exponent` is $e$ in the formulas
  exprt bin_exponent=get_exponent(f, float_spec);

  // $m$ from the formula is a value between 0.0 and 2.0 represented
  // with values in the range 0x000000 0xFFFFFF so 1 corresponds to 0x800000.
  // `bin_significand_int` represents $m * 0x800000$
  exprt bin_significand_int=
    get_significand(f, float_spec, unsignedbv_typet(32));
  // `bin_significand` represents $m$ and is obtained
  // by multiplying `binary_significand_as_int` by
  // 1/0x800000 = 2^-23 = 1.1920928955078125 * 10^-7
  exprt bin_significand=floatbv_mult(
    floatbv_typecast_exprt(bin_significand_int, round_to_zero_expr, float_type),
    constant_float(1.1920928955078125e-7, float_spec));

  // This is a first approximation of the exponent that will adjust
  // if the fraction we get is greater than 10
  exprt dec_exponent_estimate=estimate_decimal_exponent(f, float_spec);

  // Table for values of $2^x / 10^(floor(log_10(2)*x))$ where x=Range[0,128]
  std::vector<double> two_power_e_over_ten_power_d_table(
    { 1, 2, 4, 8, 1.6, 3.2, 6.4, 1.28, 2.56,
      5.12, 1.024, 2.048, 4.096, 8.192, 1.6384, 3.2768, 6.5536,
      1.31072, 2.62144, 5.24288, 1.04858, 2.09715, 4.19430, 8.38861, 1.67772,
      3.35544, 6.71089, 1.34218, 2.68435, 5.36871, 1.07374, 2.14748, 4.29497,
      8.58993, 1.71799, 3.43597, 6.87195, 1.37439, 2.74878, 5.49756, 1.09951,
      2.19902, 4.39805, 8.79609, 1.75922, 3.51844, 7.03687, 1.40737, 2.81475,
      5.62950, 1.12590, 2.25180, 4.50360, 9.00720, 1.80144, 3.60288, 7.20576,
      1.44115, 2.88230, 5.76461, 1.15292, 2.30584, 4.61169, 9.22337, 1.84467,
      3.68935, 7.37870, 1.47574, 2.95148, 5.90296, 1.18059, 2.36118, 4.72237,
      9.44473, 1.88895, 3.77789, 7.55579, 1.51116, 3.02231, 6.04463, 1.20893,
      2.41785, 4.83570, 9.67141, 1.93428, 3.86856, 7.73713, 1.54743, 3.09485,
      6.18970, 1.23794, 2.47588, 4.95176, 9.90352, 1.98070, 3.96141, 7.92282,
      1.58456, 3.16913, 6.33825, 1.26765, 2.53530, 5.07060, 1.01412, 2.02824,
      4.05648, 8.11296, 1.62259, 3.24519, 6.49037, 1.29807, 2.59615, 5.1923,
      1.03846, 2.07692, 4.15384, 8.30767, 1.66153, 3.32307, 6.64614, 1.32923,
      2.65846, 5.31691, 1.06338, 2.12676, 4.25353, 8.50706, 1.70141});

  // Table for values of $2^x / 10^(floor(log_10(2)*x))$ where x=Range[-128,-1]
  std::vector<double> two_power_e_over_ten_power_d_table_negatives(
    { 2.93874, 5.87747, 1.17549, 2.35099, 4.70198, 9.40395, 1.88079, 3.76158,
      7.52316, 1.50463, 3.00927, 6.01853, 1.20371, 2.40741, 4.81482, 9.62965,
      1.92593, 3.85186, 7.70372, 1.54074, 3.08149, 6.16298, 1.23260, 2.46519,
      4.93038, 9.86076, 1.97215, 3.94430, 7.88861, 1.57772, 3.15544, 6.31089,
      1.26218, 2.52435, 5.04871, 1.00974, 2.01948, 4.03897, 8.07794, 1.61559,
      3.23117, 6.46235, 1.29247, 2.58494, 5.16988, 1.03398, 2.06795, 4.13590,
      8.27181, 1.65436, 3.30872, 6.61744, 1.32349, 2.64698, 5.29396, 1.05879,
      2.11758, 4.23516, 8.47033, 1.69407, 3.38813, 6.77626, 1.35525, 2.71051,
      5.42101, 1.08420, 2.16840, 4.33681, 8.67362, 1.73472, 3.46945, 6.93889,
      1.38778, 2.77556, 5.55112, 1.11022, 2.22045, 4.44089, 8.88178, 1.77636,
      3.55271, 7.10543, 1.42109, 2.84217, 5.68434, 1.13687, 2.27374, 4.54747,
      9.09495, 1.81899, 3.63798, 7.27596, 1.45519, 2.91038, 5.82077, 1.16415,
      2.32831, 4.65661, 9.31323, 1.86265, 3.72529, 7.45058, 1.49012, 2.98023,
      5.96046, 1.19209, 2.38419, 4.76837, 9.53674, 1.90735, 3.81470, 7.62939,
      1.52588, 3.05176, 6.10352, 1.22070, 2.44141, 4.88281, 9.76563, 1.95313,
      3.90625, 7.81250, 1.56250, 3.12500, 6.25000, 1.25000, 2.50000, 5});

  // bias_table used to find the bias factor
  exprt conversion_factor_table_size=from_integer(
    two_power_e_over_ten_power_d_table_negatives.size()+
      two_power_e_over_ten_power_d_table.size(),
    int_type);
  array_exprt conversion_factor_table(
    array_typet(float_type, conversion_factor_table_size));
  for(const auto &f : two_power_e_over_ten_power_d_table_negatives)
    conversion_factor_table.copy_to_operands(constant_float(f, float_spec));
  for(const auto &f : two_power_e_over_ten_power_d_table)
    conversion_factor_table.copy_to_operands(constant_float(f, float_spec));

  // The index in the table, corresponding to exponent e is e+128
  plus_exprt shifted_index(bin_exponent, from_integer(128, int_type));

  // bias_factor is $2^e / 10^(floor(log_10(2)*e))$ that is $2^e/10^d$
  index_exprt conversion_factor(
    conversion_factor_table, shifted_index, float_type);

  // `dec_significand` is $n = m * bias_factor$
  exprt dec_significand=floatbv_mult(conversion_factor, bin_significand);
  exprt dec_significand_int=round_expr_to_zero(dec_significand);

  // `dec_exponent` is $d$ in the formulas
  // it is obtained from the approximation, checking whether it is not too small
  binary_relation_exprt estimate_too_small(
    dec_significand_int, ID_ge, from_integer(10, int_type));
  if_exprt decimal_exponent(
    estimate_too_small,
    plus_exprt(dec_exponent_estimate, from_integer(1, int_type)),
    dec_exponent_estimate);

  // `dec_significand` is divided by 10 if it exceeds 10
  dec_significand=if_exprt(
    estimate_too_small,
    floatbv_mult(dec_significand, constant_float(0.1, float_spec)),
    dec_significand);
  dec_significand_int=round_expr_to_zero(dec_significand);
  array_string_exprt string_expr_integer_part =
    array_pool.fresh_string(index_type, char_type);
  auto result1 = add_axioms_for_string_of_int(
    fresh_symbol, string_expr_integer_part, dec_significand_int, 3, ns);
  minus_exprt fractional_part(
    dec_significand, floatbv_of_int_expr(dec_significand_int, float_spec));

  // shifted_float is floor(f * 1e5)
  exprt shifting=constant_float(1e5, float_spec);
  exprt shifted_float=
    round_expr_to_zero(floatbv_mult(fractional_part, shifting));

  // Numbers with greater or equal value to the following, should use
  // the exponent notation.
  exprt max_non_exponent_notation=from_integer(100000, shifted_float.type());

  // fractional_part_shifted is floor(f * 100000) % 100000
  const mod_exprt fractional_part_shifted(
    shifted_float, max_non_exponent_notation);

  array_string_exprt string_fractional_part =
    array_pool.fresh_string(index_type, char_type);
  auto result2 = add_axioms_for_fractional_part(
    fresh_symbol, string_fractional_part, fractional_part_shifted, 6);

  // string_expr_with_fractional_part =
  //   concat(string_with_do, string_fractional_part)
  const array_string_exprt string_expr_with_fractional_part =
    array_pool.fresh_string(index_type, char_type);
  auto result3 = add_axioms_for_concat(
    fresh_symbol,
    string_expr_with_fractional_part,
    string_expr_integer_part,
    string_fractional_part);

  // string_expr_with_E = concat(string_fraction, string_lit_E)
  const array_string_exprt stringE =
    array_pool.fresh_string(index_type, char_type);
  auto result4 = add_axioms_for_constant(stringE, "E");
  const array_string_exprt string_expr_with_E =
    array_pool.fresh_string(index_type, char_type);
  auto result5 = add_axioms_for_concat(
    fresh_symbol,
    string_expr_with_E,
    string_expr_with_fractional_part,
    stringE);

  // exponent_string = string_of_int(decimal_exponent)
  const array_string_exprt exponent_string =
    array_pool.fresh_string(index_type, char_type);
  auto result6 = add_axioms_for_string_of_int(
    fresh_symbol, exponent_string, decimal_exponent, 3, ns);

  // string_expr = concat(string_expr_with_E, exponent_string)
  auto result7 = add_axioms_for_concat(
    fresh_symbol, res, string_expr_with_E, exponent_string);

  const exprt return_code = maximum(
    result1.first,
    maximum(
      result2.first,
      maximum(
        result3.first,
        maximum(
          result4.first,
          maximum(result5.first, maximum(result6.first, result7.first))))));
  merge(result7.second, std::move(result1.second));
  merge(result7.second, std::move(result2.second));
  merge(result7.second, std::move(result3.second));
  merge(result7.second, std::move(result4.second));
  merge(result7.second, std::move(result5.second));
  merge(result7.second, std::move(result6.second));
  return {return_code, std::move(result7.second)};
}

/// Representation of a float value in scientific notation
///
/// Add axioms corresponding to the scientific representation of floating point
/// values
/// \param fresh_symbol: generator of fresh symbols
/// \param f: a function application expression
/// \param array_pool: pool of arrays representing strings
/// \param ns: namespace
/// \return code 0 on success
std::pair<exprt, string_constraintst> add_axioms_from_float_scientific_notation(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool,
  const namespacet &ns)
{
  PRECONDITION(f.arguments().size() == 3);
  const array_string_exprt res =
    char_array_of_pointer(array_pool, f.arguments()[1], f.arguments()[0]);
  const exprt &arg = f.arguments()[2];
  return add_axioms_from_float_scientific_notation(
    fresh_symbol, res, arg, array_pool, ns);
}
