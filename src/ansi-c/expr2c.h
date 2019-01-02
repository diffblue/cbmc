/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_EXPR2C_H
#define CPROVER_ANSI_C_EXPR2C_H

#include <string>

class exprt;
class namespacet;
class typet;

/// Used for configuring the behaviour of expr2c and type2c
struct expr2c_configurationt final
{
  /// When printing struct_typet or struct_exprt, include the artificial padding
  /// components introduced to keep the struct aligned.
  bool include_struct_padding_components;

  /// When printing a struct_typet, should the components of the struct be
  /// printed inline.
  bool print_struct_body_in_type;

  /// When printing array_typet, should the size of the array be printed
  bool include_array_size;

  /// This is the string that will be printed for the true boolean expression
  std::string true_string;

  /// This is the string that will be printed for the false boolean expression
  std::string false_string;

  expr2c_configurationt(
    const bool include_struct_padding_components,
    const bool print_struct_body_in_type,
    const bool include_array_size,
    const std::string &true_string,
    const std::string &false_string)
    : include_struct_padding_components(include_struct_padding_components),
      print_struct_body_in_type(print_struct_body_in_type),
      include_array_size(include_array_size),
      true_string(true_string),
      false_string(false_string)
  {
  }

  /// This prints a human readable C like syntax that closely mirrors the
  /// internals of the GOTO program
  static expr2c_configurationt default_configuration;

  /// This prints compilable C that loses some of the internal details of the
  /// GOTO program
  static expr2c_configurationt clean_configuration;
};

std::string expr2c(const exprt &expr, const namespacet &ns);

std::string expr2c(
  const exprt &expr,
  const namespacet &ns,
  const expr2c_configurationt &configuration);

std::string type2c(const typet &type, const namespacet &ns);

std::string type2c(
  const typet &type,
  const namespacet &ns,
  const expr2c_configurationt &configuration);

std::string type2c(
  const typet &type,
  const std::string &identifier,
  const namespacet &ns,
  const expr2c_configurationt &configuration);

#endif // CPROVER_ANSI_C_EXPR2C_H
