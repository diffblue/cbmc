//
// Author: Enrico Steffinlongo for Diffblue Ltd
//

#include <util/c_types.h>
#include <util/config.h>
#include <util/cprover_prefix.h>
#include <util/expr.h>
#include <util/string_constant.h>

#include "c_typecheck_base.h"
#include "expr2c.h"

/// Function to typecheck a shadow memory field_declaration function.
/// \return a symbol of the shadow memory function
/// \throws invalid_source_file_exceptiont if the typecheck fails.
static symbol_exprt typecheck_field_decl(
  const side_effect_expr_function_callt &expr,
  const irep_idt &identifier,
  const namespacet &ns)
{
  // Check correct number of arguments
  if(expr.arguments().size() != 2)
  {
    std::ostringstream error_message;
    error_message << identifier << " takes exactly 2 arguments, but "
                  << expr.arguments().size() << " were provided";
    throw invalid_source_file_exceptiont{
      error_message.str(), expr.source_location()};
  }

  const auto &arg1 = expr.arguments()[0];
  if(!can_cast_expr<string_constantt>(arg1))
  {
    // Can't declare a shadow memory field that has a name that is not a
    // constant string
    std::ostringstream error_message;
    error_message << identifier
                  << " argument 1 must be string constant (literal), but ("
                  << expr2c(arg1, ns) << ") has type `"
                  << type2c(arg1.type(), ns) << '`';
    throw invalid_source_file_exceptiont{
      error_message.str(), expr.source_location()};
  }

  // The second argument type must be either a boolean or a bitvector of size
  // less or equal to the size of a char.
  const auto &arg2 = expr.arguments()[1];
  const auto &arg2_type = arg2.type();
  const auto arg2_type_as_bv =
    type_try_dynamic_cast<bitvector_typet>(arg2_type);
  if(
    (!arg2_type_as_bv ||
     arg2_type_as_bv->get_width() > config.ansi_c.char_width) &&
    !can_cast_type<bool_typet>(arg2_type))
  {
    // Can't declare a shadow memory field with a non-boolean and non bitvector
    // type or with a bitvector type greater than 8 bit.
    std::ostringstream error_message;
    error_message << identifier
                  << " argument 2 must be a byte-sized integer, but ("
                  << expr2c(arg2, ns) << ") has type `" << type2c(arg2_type, ns)
                  << '`';
    throw invalid_source_file_exceptiont{
      error_message.str(), expr.source_location()};
  }

  // The function type is just an ellipsis, otherwise the non-ellipsis arguments
  // will be typechecked and implicitly casted.
  code_typet t({}, void_type());
  t.make_ellipsis();

  // Create the symbol with the right type.
  symbol_exprt result(identifier, std::move(t));
  result.add_source_location() = expr.source_location();
  return result;
}

/// Function to typecheck a shadow memory get_field function.
/// \return a symbol of the shadow memory function.
/// \throws invalid_source_file_exceptiont if the typecheck fails.
static symbol_exprt typecheck_get_field(
  const side_effect_expr_function_callt &expr,
  const irep_idt &identifier,
  const namespacet &ns)
{
  // Check correct number of arguments
  if(expr.arguments().size() != 2)
  {
    std::ostringstream error_message;
    error_message << identifier << " takes exactly 2 arguments, but "
                  << expr.arguments().size() << " were provided";
    throw invalid_source_file_exceptiont{
      error_message.str(), expr.source_location()};
  }

  const auto &arg1 = expr.arguments()[0];
  const auto arg1_type_as_ptr =
    type_try_dynamic_cast<pointer_typet>(arg1.type());
  if(
    !arg1_type_as_ptr || !arg1_type_as_ptr->has_subtype() ||
    to_type_with_subtype(*arg1_type_as_ptr).subtype() == empty_typet{})
  {
    // Can't get the shadow memory value of anything other than a non-void
    // pointer
    std::ostringstream error_message;
    error_message << identifier
                  << " argument 1 must be a non-void pointer, but ("
                  << expr2c(arg1, ns) << ") has type `"
                  << type2c(arg1.type(), ns)
                  << "`. Insert a cast to the type that you want to access.";
    throw invalid_source_file_exceptiont{
      error_message.str(), expr.source_location()};
  }

  const auto &arg2 = expr.arguments()[1];
  if(!can_cast_expr<string_constantt>(arg2))
  {
    // Can't get value from a shadow memory field that has a name that is
    // not a constant string
    std::ostringstream error_message;
    error_message << identifier
                  << " argument 2 must be string constant (literal), but ("
                  << expr2c(arg2, ns) << ") has type `"
                  << type2c(arg2.type(), ns) << '`';
    throw invalid_source_file_exceptiont{
      error_message.str(), expr.source_location()};
  }

  // The function type is just an ellipsis, otherwise the non-ellipsis arguments
  // will be typechecked and implicitly casted.
  // Setting the return type to `signed_int_type` otherwise it was creating
  // problem with signed-unsigned char comparison. Having `signed_int_type`
  // seems to fix the issue as it contains more bits for the conversion.
  code_typet t({}, signed_int_type());
  t.make_ellipsis();

  // Create the symbol with the right type.
  symbol_exprt result(identifier, std::move(t));
  result.add_source_location() = expr.source_location();
  return result;
}

/// Function to typecheck a shadow memory set_field function.
/// \return a symbol of the shadow memory function.
/// \throws invalid_source_file_exceptiont if the typecheck fails.
static symbol_exprt typecheck_set_field(
  const side_effect_expr_function_callt &expr,
  const irep_idt &identifier,
  const namespacet &ns)
{
  // Check correct number of arguments
  if(expr.arguments().size() != 3)
  {
    std::ostringstream error_message;
    error_message << identifier << " takes exactly 3 arguments, but "
                  << expr.arguments().size() << " were provided";
    throw invalid_source_file_exceptiont{
      error_message.str(), expr.source_location()};
  }

  const auto &arg1 = expr.arguments()[0];
  const auto arg1_type_as_ptr =
    type_try_dynamic_cast<pointer_typet>(arg1.type());
  if(
    !arg1_type_as_ptr || !arg1_type_as_ptr->has_subtype() ||
    to_type_with_subtype(*arg1_type_as_ptr).subtype() == empty_typet{})
  {
    // Can't set the shadow memory value of anything other than a non-void
    // pointer
    std::ostringstream error_message;
    error_message << identifier
                  << " argument 1 must be a non-void pointer, but ("
                  << expr2c(arg1, ns) << ") has type `"
                  << type2c(arg1.type(), ns)
                  << "`. Insert a cast to the type that you want to access.";
    throw invalid_source_file_exceptiont{
      error_message.str(), expr.source_location()};
  }

  const auto &arg2 = expr.arguments()[1];
  if(!can_cast_expr<string_constantt>(arg2))
  {
    // Can't set value from a shadow memory field that has a name that is
    // not a constant string
    std::ostringstream error_message;
    error_message << identifier
                  << " argument 2 must be string constant (literal), but ("
                  << expr2c(arg2, ns) << ") has type `"
                  << type2c(arg2.type(), ns) << '`';
    throw invalid_source_file_exceptiont{
      error_message.str(), expr.source_location()};
  }

  // The third argument type must be either a boolean or a bitvector.
  const auto &arg3 = expr.arguments()[2];
  const auto &arg3_type = arg3.type();
  if(
    !can_cast_type<bitvector_typet>(arg3_type) &&
    !can_cast_type<bool_typet>(arg3_type))
  {
    // Can't set the shadow memory value with a non-boolean and non-bitvector
    // value.
    std::ostringstream error_message;
    error_message << identifier
                  << " argument 3 must be a boolean or of integer value, but ("
                  << expr2c(arg3, ns) << ") has type `" << type2c(arg3_type, ns)
                  << '`';
    throw invalid_source_file_exceptiont{
      error_message.str(), expr.source_location()};
  }

  // The function type is just an ellipsis, otherwise the non-ellipsis arguments
  // will be typechecked and implicitly casted.
  code_typet t({}, void_type());
  t.make_ellipsis();

  // Create the symbol with the right type.
  symbol_exprt result(identifier, std::move(t));
  result.add_source_location() = expr.source_location();
  return result;
}

/// Typecheck the function if it is a shadow_memory builtin and return a symbol
/// for it. Otherwise return empty.
std::optional<symbol_exprt> c_typecheck_baset::typecheck_shadow_memory_builtin(
  const side_effect_expr_function_callt &expr)
{
  const exprt &f_op = expr.function();
  INVARIANT(
    can_cast_expr<symbol_exprt>(f_op),
    "expr.function() has to be a symbol_expr");
  const irep_idt &identifier = to_symbol_expr(f_op).get_identifier();

  if(
    identifier == CPROVER_PREFIX "field_decl_global" ||
    identifier == CPROVER_PREFIX "field_decl_local")
  {
    return typecheck_field_decl(expr, identifier, *this);
  }
  else if(identifier == CPROVER_PREFIX "get_field")
  {
    return typecheck_get_field(expr, identifier, *this);
  }
  else if(identifier == CPROVER_PREFIX "set_field")
  {
    return typecheck_set_field(expr, identifier, *this);
  }
  // The function is not a shadow memory builtin, so we return <empty>.
  return {};
}
