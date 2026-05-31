/*******************************************************************\

Module: C++ Language Type Checking

Author:

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/expr_util.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/string_constant.h>
#include <util/symbol.h>
#include <util/symbol_table_base.h>

#include <ansi-c/c_qualifiers.h>

#include "cpp_sfinae_context.h"
#include "cpp_typecheck.h"
#include "cpp_util.h"

#include <functional>

/// Lvalue-to-rvalue conversion
///
///  An lvalue (3.10) of a non-function, non-array type T can be
///  converted to an rvalue. If T is an incomplete type, a program
///  that necessitates this conversion is ill-formed. If the object
///  to which the lvalue refers is not an object of type T and is
///  not an object of a type derived from T, or if the object is
///  uninitialized, a program that necessitates this conversion has
///  undefined behavior. If T is a non-class type, the type of the
///  rvalue is the cv-unqualified version of T. Otherwise, the type of
///  the rvalue is T.
///
///  The value contained in the object indicated by the lvalue
///  is the rvalue result. When an lvalue-to-rvalue conversion
///  occurs within the operand of sizeof (5.3.3) the value contained
///  in the referenced object is not accessed, since that operator
///  does not evaluate its operand.
/// \par parameters: A typechecked  lvalue expression
/// \return True iff the lvalue-to-rvalue conversion is possible. 'new_type'
///   contains the result of the conversion.
bool cpp_typecheckt::standard_conversion_lvalue_to_rvalue(
  const exprt &expr,
  exprt &new_expr) const
{
  PRECONDITION(expr.get_bool(ID_C_lvalue));

  if(expr.type().id() == ID_code)
    return false;

  if(
    expr.type().id() == ID_struct &&
    to_struct_type(expr.type()).is_incomplete())
    return false;

  if(expr.type().id() == ID_union && to_union_type(expr.type()).is_incomplete())
    return false;

  new_expr = expr;
  new_expr.remove(ID_C_lvalue);

  return true;
}

/// Array-to-pointer conversion
///
/// An lvalue or rvalue of type "array of N T" or "array of unknown
/// bound of T" can be converted to an rvalue of type "pointer to T."
/// The result is a pointer to the first element of the array.
/// \par parameters: An array expression
/// \return True iff the array-to-pointer conversion is possible. The result of
///   the conversion is stored in 'new_expr'.
bool cpp_typecheckt::standard_conversion_array_to_pointer(
  const exprt &expr,
  exprt &new_expr) const
{
  PRECONDITION(expr.type().id() == ID_array);

  index_exprt index(expr, from_integer(0, c_index_type()));

  index.set(ID_C_lvalue, true);

  new_expr = address_of_exprt(index);

  return true;
}

/// Function-to-pointer conversion
///
/// An lvalue of function type T can be converted to an rvalue of type
/// "pointer to T." The result is a pointer to the function.50)
/// \par parameters: A function expression
/// \return True iff the array-to-pointer conversion is possible. The result of
///   the conversion is stored in 'new_expr'.
bool cpp_typecheckt::standard_conversion_function_to_pointer(
  const exprt &expr,
  exprt &new_expr) const
{
  if(!expr.get_bool(ID_C_lvalue))
    return false;

  new_expr = address_of_exprt(expr);

  return true;
}

/// Qualification conversion
/// \par parameters: A typechecked expression 'expr', a destination
/// type 'type'
/// \return True iff the qualification conversion is possible. The result of the
///   conversion is stored in 'new_expr'.
bool cpp_typecheckt::standard_conversion_qualification(
  const exprt &expr,
  const typet &type,
  exprt &new_expr) const
{
  if(expr.type().id() != ID_pointer || is_reference(expr.type()))
    return false;

  if(expr.get_bool(ID_C_lvalue))
    return false;

  if(expr.type() != type)
    return false;

  typet sub_from = to_pointer_type(expr.type()).base_type();
  typet sub_to = to_pointer_type(type).base_type();
  bool const_to = true;

  while(sub_from.id() == ID_pointer)
  {
    c_qualifierst qual_from(sub_from);
    c_qualifierst qual_to(sub_to);

    if(!qual_to.is_constant)
      const_to = false;

    if(qual_from.is_constant && !qual_to.is_constant)
      return false;

    if(qual_from != qual_to && !const_to)
      return false;

    typet tmp1 = to_pointer_type(sub_from).base_type();
    sub_from.swap(tmp1);

    typet tmp2 = sub_to.add_subtype();
    sub_to.swap(tmp2);
  }

  c_qualifierst qual_from(sub_from);
  c_qualifierst qual_to(sub_to);

  if(qual_from.is_subset_of(qual_to))
  {
    new_expr = expr;
    new_expr.type() = type;
    return true;
  }

  return false;
}

/// Integral-promotion conversion
///
/// An rvalue of type char, signed char, unsigned char, short int,
/// or unsigned short int can be converted to an rvalue of type int
/// if int can represent all the values of the source type; otherwise,
/// the source rvalue can be converted to an rvalue of type unsigned int.
///
/// An rvalue of type wchar_t (3.9.1) or an enumeration type (7.2) can
/// be converted to an rvalue of the first of the following types that
/// can represent all the values of its underlying type: int, unsigned int,
/// long, or unsigned long.
///
/// An rvalue for an integral bit-field (9.6) can be converted
/// to an rvalue of type int if int can represent all the values of the
/// bit-field; otherwise, it can be converted to unsigned int if
/// unsigned int can represent all the values of the bit-field.
/// If the bit-field is larger yet, no integral promotion applies to
/// it. If the bit-field has an enumerated type, it is treated as
/// any other value of that type for promotion purposes.
///
/// An rvalue of type bool can be converted to an rvalue of type int,
/// with false becoming zero and true becoming one.
/// \par parameters: A typechecked expression 'expr'
/// \return True iff the integral promotion is possible. The result of the
///   conversion is stored in 'new_expr'.
bool cpp_typecheckt::standard_conversion_integral_promotion(
  const exprt &expr,
  exprt &new_expr) const
{
  if(expr.get_bool(ID_C_lvalue))
    return false;

  c_qualifierst qual_from;
  qual_from.read(expr.type());

  typet int_type = signed_int_type();
  qual_from.write(int_type);

  if(expr.type().id() == ID_signedbv)
  {
    std::size_t width = to_signedbv_type(expr.type()).get_width();
    if(width >= config.ansi_c.int_width)
      return false;
    new_expr = typecast_exprt(expr, int_type);
    return true;
  }

  if(expr.type().id() == ID_unsignedbv)
  {
    std::size_t width = to_unsignedbv_type(expr.type()).get_width();
    if(width >= config.ansi_c.int_width)
      return false;
    new_expr = typecast_exprt(expr, int_type);
    return true;
  }

  if(expr.is_boolean() || expr.type().id() == ID_c_bool)
  {
    new_expr = typecast_exprt(expr, int_type);
    return true;
  }

  if(expr.type().id() == ID_c_enum_tag)
  {
    new_expr = typecast_exprt(expr, int_type);
    return true;
  }

  return false;
}

/// Floating-point-promotion conversion
///
/// An rvalue of type float can be converted to an rvalue of type
/// double. The value is unchanged.
/// \par parameters: A typechecked expression 'expr'
/// \return True iff the integral promotion is possible. The result of the
///   conversion is stored in 'new_expr'.
bool cpp_typecheckt::standard_conversion_floating_point_promotion(
  const exprt &expr,
  exprt &new_expr) const
{
  if(expr.get_bool(ID_C_lvalue))
    return false;

  // we only do that with 'float',
  // not with 'double' or 'long double'
  if(expr.type() != float_type())
    return false;

  std::size_t width = to_floatbv_type(expr.type()).get_width();

  if(width != config.ansi_c.single_width)
    return false;

  c_qualifierst qual_from;
  qual_from.read(expr.type());

  new_expr = typecast_exprt(expr, double_type());
  qual_from.write(new_expr.type());

  return true;
}

/// Integral conversion
///
/// An rvalue of type char, signed char, unsigned char, short int,
/// An rvalue of an integer type can be converted to an rvalue of
/// another integer type. An rvalue of an enumeration type can be
/// converted to an rvalue of an integer type.
///
/// If the destination type is unsigned, the resulting value is the
/// least unsigned integer congruent to the source integer (modulo
/// 2n where n is the number of bits used to represent the unsigned
/// type). [Note: In a two's complement representation, this
/// conversion is conceptual and there is no change in the bit
/// pattern (if there is no truncation). ]
///
/// If the destination type is signed, the value is unchanged if it
/// can be represented in the destination type (and bit-field width);
/// otherwise, the value is implementation-defined.
///
/// If the destination type is bool, see 4.12. If the source type is
/// bool, the value false is converted to zero and the value true is
/// converted to one.
///
/// The conversions allowed as integral promotions are excluded from
/// the set of integral conversions.
/// \par parameters: A typechecked expression 'expr', a destination
/// type 'type'
/// \return True iff the integral promotion is possible. The result of the
///   conversion is stored in 'new_expr'.
bool cpp_typecheckt::standard_conversion_integral_conversion(
  const exprt &expr,
  const typet &type,
  exprt &new_expr) const
{
  if(type.id() != ID_signedbv && type.id() != ID_unsignedbv)
    return false;

  if(
    expr.type().id() != ID_signedbv && expr.type().id() != ID_unsignedbv &&
    expr.type().id() != ID_c_bool && !expr.is_boolean() &&
    expr.type().id() != ID_c_enum_tag)
  {
    return false;
  }

  if(expr.get_bool(ID_C_lvalue))
    return false;

  c_qualifierst qual_from;
  qual_from.read(expr.type());
  new_expr = typecast_exprt::conditional_cast(expr, type);
  qual_from.write(new_expr.type());

  return true;
}

/// Floating-integral conversion
///
/// An rvalue of a floating point type can be converted to an rvalue
/// of an integer type. The conversion truncates; that is, the
/// fractional part is discarded. The behavior is undefined if the
/// truncated value cannot be represented in the destination type.
/// [Note: If the destination type is bool, see 4.12. ]
///
/// An rvalue of an integer type or of an enumeration type can be
/// converted to an rvalue of a floating point type. The result is
/// exact if possible. Otherwise, it is an implementation-defined
/// choice of either the next lower or higher representable value.
/// [Note: loss of precision occurs if the integral value cannot be
/// represented exactly as a value of the floating type. ] If the
/// source type is bool, the value false is converted to zero and the
/// value true is converted to one.
/// \par parameters: A typechecked expression 'expr'
/// \return True iff the conversion is possible. The result of the conversion is
///   stored in 'new_expr'.
bool cpp_typecheckt::standard_conversion_floating_integral_conversion(
  const exprt &expr,
  const typet &type,
  exprt &new_expr) const
{
  if(expr.get_bool(ID_C_lvalue))
    return false;

  if(expr.type().id() == ID_floatbv || expr.type().id() == ID_fixedbv)
  {
    if(type.id() != ID_signedbv && type.id() != ID_unsignedbv)
      return false;
  }
  else if(
    expr.type().id() == ID_signedbv || expr.type().id() == ID_unsignedbv ||
    expr.type().id() == ID_c_enum_tag)
  {
    if(type.id() != ID_fixedbv && type.id() != ID_floatbv)
      return false;
  }
  else
    return false;

  c_qualifierst qual_from;
  qual_from.read(expr.type());
  new_expr = typecast_exprt::conditional_cast(expr, type);
  qual_from.write(new_expr.type());

  return true;
}

/// Floating-point conversion
///
/// An rvalue of floating point type can be converted to an rvalue
/// of another floating point type. If the source value can be exactly
/// represented in the destination type, the result of the conversion
/// is that exact representation. If the source value is between two
/// adjacent destination values, the result of the conversion is an
/// implementation-defined choice of either of those values. Otherwise,
/// the behavior is undefined.
///
/// The conversions allowed as floating point promotions are excluded
/// from the set of floating point conversions.
/// \par parameters: A typechecked expression 'expr', a destination
/// type 'type'
/// \return True iff the floating-point conversion is possible. The result of
///   the conversion is stored in 'new_expr'.
bool cpp_typecheckt::standard_conversion_floating_point_conversion(
  const exprt &expr,
  const typet &type,
  exprt &new_expr) const
{
  if(expr.type().id() != ID_floatbv && expr.type().id() != ID_fixedbv)
    return false;

  if(type.id() != ID_floatbv && type.id() != ID_fixedbv)
    return false;

  if(expr.get_bool(ID_C_lvalue))
    return false;

  c_qualifierst qual_from;

  qual_from.read(expr.type());
  new_expr = typecast_exprt::conditional_cast(expr, type);
  qual_from.write(new_expr.type());

  return true;
}

/// Pointer conversion
///
/// A null pointer constant is an integral constant expression
/// (5.19) rvalue of integer type that evaluates to zero. A null
/// pointer constant can be converted to a pointer type; the result
/// is the null pointer value of that type and is distinguishable
/// from every other value of pointer to object or pointer to
/// function type. Two null pointer values of the same type shall
/// compare equal. The conversion of a null pointer constant to a
/// pointer to cv-qualified type is a single conversion, and not the
/// sequence of a pointer conversion followed by a qualification
/// conversion (4.4).
///
/// An rvalue of type "pointer to cv T," where T is an object type,
/// can be converted to an rvalue of type "pointer to cv void." The
/// result of converting a "pointer to cv T" to a "pointer to cv
/// void" points to the start of the storage location where the
/// object of type T resides, as if the object is a most derived
/// object (1.8) of type T (that is, not a base class subobject).
///
/// An rvalue of type "pointer to cv D," where D is a class type,
/// can be converted to an rvalue of type "pointer to cv B," where
/// B is a base class (clause 10) of D. If B is an inaccessible
/// (clause 11) or ambiguous (10.2) base class of D, a program that
/// necessitates this conversion is ill-formed. The result of the
/// conversion is a pointer to the base class sub-object of the
/// derived class object. The null pointer value is converted to
/// the null pointer value of the destination type.
/// \par parameters: A typechecked expression 'expr', a destination
/// type 'type'
/// \return True iff the pointer conversion is possible. The result of the
///   conversion is stored in 'new_expr'.
bool cpp_typecheckt::standard_conversion_pointer(
  const exprt &expr,
  const typet &type,
  exprt &new_expr)
{
  if(type.id() != ID_pointer || is_reference(type))
    return false;

  if(expr.get_bool(ID_C_lvalue))
    return false;

  // integer 0 to NULL pointer conversion?
  if(simplify_expr(expr, *this) == 0 && expr.type().id() != ID_pointer)
  {
    new_expr = expr;
    new_expr.set(ID_value, ID_NULL);
    new_expr.type() = type;
    return true;
  }

  if(type.find(ID_to_member).is_not_nil())
    return false;

  if(
    expr.type().id() != ID_pointer ||
    expr.type().find(ID_to_member).is_not_nil())
  {
    return false;
  }

  const pointer_typet &pointer_type = to_pointer_type(type);
  const typet &sub_from = to_pointer_type(expr.type()).base_type();
  const typet &sub_to = pointer_type.base_type();

  // std::nullptr_t to _any_ pointer type
  if(sub_from.id() == ID_nullptr)
    return true;

  // anything but function pointer to void *
  if(sub_from.id() != ID_code && sub_to.id() == ID_empty)
  {
    c_qualifierst qual_from;
    qual_from.read(to_pointer_type(expr.type()).base_type());
    new_expr = typecast_exprt::conditional_cast(expr, type);
    qual_from.write(to_pointer_type(new_expr.type()).base_type());
    return true;
  }

  // struct * to struct *
  if(sub_from.id() == ID_struct_tag && sub_to.id() == ID_struct_tag)
  {
    const struct_typet &from_struct = follow_tag(to_struct_tag_type(sub_from));
    const struct_typet &to_struct = follow_tag(to_struct_tag_type(sub_to));
    if(
      subtype_typecast(from_struct, to_struct) &&
      base_publicly_accessible(from_struct, to_struct))
    {
      c_qualifierst qual_from;
      qual_from.read(to_pointer_type(expr.type()).base_type());
      new_expr = expr;
      make_ptr_typecast(new_expr, pointer_type);
      qual_from.write(to_pointer_type(new_expr.type()).base_type());
      return true;
    }
  }

  return false;
}

/// Pointer-to-member conversion
///
/// A null pointer constant (4.10) can be converted to a pointer to
/// member type; the result is the null member pointer value of that
/// type and is distinguishable from any pointer to member not created
/// from a null pointer constant. Two null member pointer values of
/// the same type shall compare equal. The conversion of a null pointer
/// constant to a pointer to member of cv-qualified type is a single
/// conversion, and not the sequence of a pointer to member conversion
/// followed by a qualification conversion (4.4).
///
/// An rvalue of type "pointer to member of B of type cv T," where B
/// is a class type, can be converted to an rvalue of type "pointer
/// to member of D of type cv T," where D is a derived class
/// (clause 10) of B. If B is an inaccessible (clause 11), ambiguous
/// (10.2) or virtual (10.1) base class of D, a program that
/// necessitates this conversion is ill-formed. The result of the
/// conversion refers to the same member as the pointer to member
/// before the conversion took place, but it refers to the base class
/// member as if it were a member of the derived class. The result
/// refers to the member in D"s instance of B. Since the result has
/// type "pointer to member of D of type cv T," it can be dereferenced
/// with a D object. The result is the same as if the pointer to
/// member of B were dereferenced with the B sub-object of D. The null
/// member pointer value is converted to the null member pointer value
/// of the destination type.52)
/// \par parameters: A typechecked expression 'expr', a destination
/// type 'type'
/// \return True iff the pointer-to-member conversion is possible. The result of
///   the conversion is stored in 'new_expr'.
bool cpp_typecheckt::standard_conversion_pointer_to_member(
  const exprt &expr,
  const typet &type,
  exprt &new_expr)
{
  if(
    type.id() != ID_pointer || is_reference(type) ||
    type.find(ID_to_member).is_nil())
  {
    return false;
  }

  if(expr.type().id() != ID_pointer || expr.type().find(ID_to_member).is_nil())
    return false;

  if(
    to_pointer_type(type).base_type() !=
    to_pointer_type(expr.type()).base_type())
  {
    // base types are different
    if(
      to_pointer_type(type).base_type().id() == ID_code &&
      to_pointer_type(expr.type()).base_type().id() == ID_code)
    {
      code_typet code1 = to_code_type(to_pointer_type(expr.type()).base_type());
      DATA_INVARIANT(!code1.parameters().empty(), "must have parameters");
      code_typet::parametert this1 = code1.parameters()[0];
      INVARIANT(this1.get_this(), "first parameter should be `this'");
      code1.parameters().erase(code1.parameters().begin());

      code_typet code2 = to_code_type(to_pointer_type(type).base_type());
      DATA_INVARIANT(!code2.parameters().empty(), "must have parameters");
      code_typet::parametert this2 = code2.parameters()[0];
      INVARIANT(this2.get_this(), "first parameter should be `this'");
      code2.parameters().erase(code2.parameters().begin());

      if(
        to_pointer_type(this2.type()).base_type().get_bool(ID_C_constant) &&
        !to_pointer_type(this1.type()).base_type().get_bool(ID_C_constant))
        return false;

      // give a second chance ignoring `this'
      if(code1 != code2)
        return false;
    }
    else
      return false;
  }

  if(expr.get_bool(ID_C_lvalue))
    return false;

  if(expr.is_constant() && to_constant_expr(expr).is_null_pointer())
  {
    new_expr = typecast_exprt::conditional_cast(expr, type);
    return true;
  }

  const struct_typet &from_struct = follow_tag(to_struct_tag_type(
    static_cast<const typet &>(expr.type().find(ID_to_member))));

  const struct_typet &to_struct = follow_tag(
    to_struct_tag_type(static_cast<const typet &>(type.find(ID_to_member))));

  if(subtype_typecast(to_struct, from_struct))
  {
    new_expr = typecast_exprt::conditional_cast(expr, type);
    return true;
  }

  return false;
}

/// Boolean conversion
///
/// An rvalue of arithmetic, enumeration, pointer, or pointer to
/// member type can be converted to an rvalue of type bool.
/// A zero value, null pointer value, or null member pointer value is
/// converted to false; any other value is converted to true.
/// \par parameters: A typechecked expression 'expr'
/// \return True iff the boolean conversion is possible. The result of the
///   conversion is stored in 'new_expr'.
bool cpp_typecheckt::standard_conversion_boolean(
  const exprt &expr,
  exprt &new_expr) const
{
  if(expr.get_bool(ID_C_lvalue))
    return false;

  if(
    expr.type().id() != ID_signedbv && expr.type().id() != ID_unsignedbv &&
    expr.type().id() != ID_pointer && !expr.is_boolean() &&
    expr.type().id() != ID_c_enum_tag)
  {
    return false;
  }

  c_qualifierst qual_from;
  qual_from.read(expr.type());

  typet Bool = c_bool_type();
  qual_from.write(Bool);

  new_expr = typecast_exprt::conditional_cast(expr, Bool);
  return true;
}

/// Standard Conversion Sequence
///
/// A standard conversion sequence is a sequence of standard conversions
/// in the following order:
///
/// * Zero or one conversion from the following set: lvalue-to-rvalue
///   conversion, array-to-pointer conversion, and function-to-pointer
///   conversion.
///
/// * Zero or one conversion from the following set: integral
///   promotions, floating point promotion, integral conversions,
///   floating point conversions, floating-integral conversions,
///   pointer conversions, pointer to member conversions, and boolean
///   conversions.
///
/// * Zero or one qualification conversion.
/// \par parameters: A typechecked expression 'expr', a destination
/// type 'type'.
/// \return True iff a standard conversion sequence exists. The result of the
///   conversion is stored in 'new_expr'. The reference 'rank' is incremented.
bool cpp_typecheckt::standard_conversion_sequence(
  const exprt &expr,
  const typet &type,
  exprt &new_expr,
  unsigned &rank)
{
  PRECONDITION(!is_reference(expr.type()) && !is_reference(type));

  exprt curr_expr = expr;

  // bit fields are converted like their underlying type
  if(type.id() == ID_c_bit_field)
    return standard_conversion_sequence(
      expr, to_c_bit_field_type(type).underlying_type(), new_expr, rank);

  // we turn bit fields into their underlying type
  if(curr_expr.type().id() == ID_c_bit_field)
    curr_expr = typecast_exprt(
      curr_expr, to_c_bit_field_type(curr_expr.type()).underlying_type());

  if(curr_expr.type().id() == ID_array)
  {
    if(type.id() == ID_pointer)
    {
      if(!standard_conversion_array_to_pointer(curr_expr, new_expr))
        return false;
    }
  }
  else if(curr_expr.type().id() == ID_code && type.id() == ID_pointer)
  {
    if(!standard_conversion_function_to_pointer(curr_expr, new_expr))
      return false;
  }
  else if(curr_expr.get_bool(ID_C_lvalue))
  {
    if(!standard_conversion_lvalue_to_rvalue(curr_expr, new_expr))
      return false;
  }
  else
    new_expr = curr_expr;

  curr_expr.swap(new_expr);

  // two enums are the same if the tag is the same,
  // even if the width differs (enum bit-fields!)
  if(type.id() == ID_c_enum_tag && curr_expr.type().id() == ID_c_enum_tag)
  {
    if(
      to_tag_type(type).get_identifier() ==
      to_tag_type(curr_expr.type()).get_identifier())
    {
      return true;
    }
    else
    {
      // In contrast to C, we simply don't allow implicit conversions
      // between enums.
      return false;
    }
  }

  // need to consider #c_type
  if(
    curr_expr.type() != type ||
    curr_expr.type().get(ID_C_c_type) != type.get(ID_C_c_type))
  {
    if(
      type.id() == ID_signedbv || type.id() == ID_unsignedbv ||
      type.id() == ID_c_enum_tag)
    {
      if(
        !standard_conversion_integral_promotion(curr_expr, new_expr) ||
        new_expr.type() != type)
      {
        if(!standard_conversion_integral_conversion(curr_expr, type, new_expr))
        {
          if(!standard_conversion_floating_integral_conversion(
               curr_expr, type, new_expr))
            return false;
        }

        rank += 3;
      }
      else
        rank += 2;
    }
    else if(type.id() == ID_floatbv || type.id() == ID_fixedbv)
    {
      if(
        !standard_conversion_floating_point_promotion(curr_expr, new_expr) ||
        new_expr.type() != type)
      {
        if(
          !standard_conversion_floating_point_conversion(
            curr_expr, type, new_expr) &&
          !standard_conversion_floating_integral_conversion(
            curr_expr, type, new_expr))
          return false;

        rank += 3;
      }
      else
        rank += 2;
    }
    else if(type.id() == ID_pointer)
    {
      if(
        expr.type().id() == ID_pointer &&
        to_pointer_type(expr.type()).base_type().id() == ID_nullptr)
      {
        // std::nullptr_t to _any_ pointer type is ok
        new_expr = typecast_exprt::conditional_cast(new_expr, type);
      }
      else if(!standard_conversion_pointer(curr_expr, type, new_expr))
      {
        if(!standard_conversion_pointer_to_member(curr_expr, type, new_expr))
          return false;
      }

      rank += 3;
    }
    else if(type.id() == ID_c_bool)
    {
      if(!standard_conversion_boolean(curr_expr, new_expr))
        return false;

      rank += 3;
    }
    else if(type.id() == ID_bool)
    {
      if(
        curr_expr.type().id() == ID_signedbv ||
        curr_expr.type().id() == ID_unsignedbv ||
        curr_expr.type().id() == ID_floatbv ||
        curr_expr.type().id() == ID_fixedbv ||
        curr_expr.type().id() == ID_pointer ||
        curr_expr.type().id() == ID_c_bool ||
        curr_expr.type().id() == ID_c_enum_tag)
      {
        new_expr = is_not_zero(curr_expr, *this);
      }
      else
        return false;

      rank += 3;
    }
    else
      return false;
  }
  else
    new_expr = curr_expr;

  curr_expr.swap(new_expr);

  if(curr_expr.type().id() == ID_pointer)
  {
    typet sub_from = curr_expr.type();
    typet sub_to = type;

    do
    {
      typet tmp_from = to_pointer_type(sub_from).base_type();
      sub_from.swap(tmp_from);
      typet tmp_to = sub_to.add_subtype();
      sub_to.swap(tmp_to);

      c_qualifierst qual_from;
      qual_from.read(sub_from);

      c_qualifierst qual_to;
      qual_to.read(sub_to);

      if(qual_from != qual_to)
      {
        rank += 1;
        break;
      }
    } while(sub_from.id() == ID_pointer);

    if(!standard_conversion_qualification(curr_expr, type, new_expr))
      return false;
  }
  else
  {
    new_expr = curr_expr;
    new_expr.type() = type;
  }

  return true;
}

/// Phase 4B: per [temp.deduct.conv]/1, deduce template arguments
/// for a conversion-function template by unifying the template's
/// return type (P) with the destination type (A).
///
/// Called from `user_defined_conversion_sequence` for the case where
/// the source class has a `has_template_conversion_operator` flag
/// (set by `typecheck_compound_body` in
/// `cpp_typecheck_compound_type.cpp`).  Iterates template cast
/// operators of the source class, runs SFINAE-guarded deduction per
/// [temp.deduct]/8, applies [temp.deduct.partial]/3.2 partial
/// ordering to disambiguate when multiple specialisations would
/// be viable for the same destination type, instantiates the
/// most-specialised (or unique) match, then builds the same kind
/// of member-function call expression as the non-template path.
///
/// Per [over.ics.user]/3 the second standard conversion sequence
/// after the user-defined conversion shall have Exact Match rank,
/// which is enforced here by requiring the post-deduction standard
/// conversion to add zero rank.
///
/// Returns `true` on a successful unambiguous deduction (after
/// partial ordering), with `new_expr` set to the typechecked
/// conversion expression and `rank` incremented by the second
/// standard conversion's rank.  Returns `false` if no candidate is
/// found, deduction fails for every candidate, or partial ordering
/// cannot pick a unique most-specialised candidate (genuine
/// ambiguity).
namespace
{
/// Result of [temp.deduct.conv]/1 deduction for a single template
/// cast operator candidate.  Used in two phases: first a deduction-
/// only collection pass, then partial ordering across the survivors,
/// then instantiation of the unique winner.
struct conversion_deduction_resultt
{
  /// The template symbol that survived deduction.
  const symbolt *cand_sym;
  /// The deduced specialisation arguments.
  cpp_template_args_tct guessed_args;
  /// The candidate's return-type pattern (P), already with
  /// [temp.deduct.conv]/2 reference-stripping applied so it can be
  /// compared via [temp.deduct.partial]/5 + /7.
  typet P_for_partial_ordering;
};
} // namespace

/// [temp.deduct.partial]/3.2: in conversion-function context, the
/// types used for partial ordering are the return types of the two
/// conversion function templates.  Returns `true` if F is at-least-
/// as-specialised as G under this rule.
///
/// Per [temp.deduct.partial]/2 + /8: deduction uses F's *transformed*
/// type as the argument (A) and G's *original* type as the parameter
/// (P).  If deduction of G's template parameters succeeds against
/// F's transformed pattern, then F's type is at-least-as-specialised
/// as G's type.  In CBMC, since template parameters carry their
/// containing scope's prefix in their identifier, F's and G's
/// parameters never collide in `template_map`, so the
/// "transformation" reduces to "treat F's parameters as concrete
/// inert types, deduce G's parameters only".
///
/// /5 (drop reference) and /7 (drop top-level cv) are applied to
/// both P and A before the deduction.
bool cpp_typecheckt::conversion_template_at_least_as_specialised(
  const cpp_declarationt &F,
  const cpp_declarationt &G,
  const irep_idt &F_scope_id,
  const irep_idt &G_scope_id)
{
  if(F.declarators().empty() || G.declarators().empty())
    return false;
  const cpp_declaratort &F_dcl = F.declarators()[0];
  const cpp_declaratort &G_dcl = G.declarators()[0];
  if(F_dcl.name().get_sub().size() < 2 || G_dcl.name().get_sub().size() < 2)
    return false;

  // Per /2 + /8: A = F's transformed, P = G's original; the
  // deduction binds G's parameters.  In CBMC's representation we
  // can use the original return types directly because F's and G's
  // parameter symbols are disjoint (different scope prefixes).
  typet A = static_cast<const typet &>(F_dcl.name().get_sub()[1]);
  typet P = static_cast<const typet &>(G_dcl.name().get_sub()[1]);

  // [temp.deduct.partial]/5: drop reference on both.  Handle both
  // post-typecheck (ID_pointer + ID_C_reference) and pre-typecheck
  // (ID_frontend_pointer + ID_C_reference) representations.
  auto strip_top_reference = [](typet &t)
  {
    if(
      (t.id() == ID_pointer || t.id() == ID_frontend_pointer) &&
      t.get_bool(ID_C_reference))
    {
      t = static_cast<const typet &>(to_type_with_subtype(t).subtype());
    }
  };
  strip_top_reference(P);
  strip_top_reference(A);

  // [temp.deduct.partial]/7: drop top-level cv on both.
  auto drop_top_cv = [](typet &t)
  {
    c_qualifierst q;
    q.read(t);
    if(q.is_constant || q.is_volatile || q.is_restricted || q.is_atomic)
    {
      c_qualifierst empty;
      empty.write(t);
    }
  };
  drop_top_cv(P);
  drop_top_cv(A);

  cpp_save_scopet save_scope{cpp_scopes};
  cpp_saved_template_mapt saved_map{template_map};

  try
  {
    sfinae_contextt sfinae_guard{*this};
    template_map.clear();
    // Mark only G's parameters as deducible — that's whose pattern
    // sits in P.  F's parameters appear in A but are not in
    // template_map, so the deduction treats them as concrete
    // (the "transformed type" trick).
    template_map.build_unassigned(G.template_type());

    // Move into G's template scope so cpp_name lookup of G's
    // parameters during deduction resolves correctly.
    auto scope_it = cpp_scopes.id_map.find(G_scope_id);
    if(scope_it != cpp_scopes.id_map.end())
      cpp_scopes.go_to(static_cast<cpp_scopet &>(*scope_it->second));

    cpp_typecheck_resolvet resolver{*this};
    resolver.guess_template_args(P, A);

    cpp_template_args_tct guessed =
      template_map.build_template_args(G.template_type());
    return !guessed.has_unassigned();
  }
  catch(...)
  {
    return false;
  }

  (void)F_scope_id; // currently unused; reserved for future
                    // synthetic-type substitution into F's pattern.
}

/// Phase 4B core helper: deduction + partial ordering + instantiation
/// for template conversion operators.  See header for the contract.
const symbolt *cpp_typecheckt::find_template_conversion_specialisation(
  const exprt &expr,
  const typet &to)
{
  if(expr.type().id() != ID_struct_tag)
    return nullptr;

  const struct_typet &from_followed =
    follow_tag(to_struct_tag_type(expr.type()));

  if(!from_followed.get_bool("has_template_conversion_operator"))
    return nullptr;

  // Determine the class scope prefix used for member symbols.  The
  // symbol_table keys members with the class's `pretty_name`-style
  // prefix (e.g., `any_t::`), not the struct-tag identifier
  // (`tag-any_t`).  Get the prefix from the tag symbol's pretty_name.
  const irep_idt &class_id_with_tag =
    to_struct_tag_type(expr.type()).get_identifier();
  const symbolt *class_sym = symbol_table.lookup(class_id_with_tag);
  if(class_sym == nullptr)
    return nullptr;
  const std::string class_prefix = id2string(class_sym->pretty_name) + "::";

  // Collect candidate template-cast-operator symbols up front: the
  // symbol_table grows during instantiation, which would invalidate
  // an in-place iterator.
  std::vector<const symbolt *> candidate_syms;
  std::vector<irep_idt> candidate_scope_ids;
  for(const auto &name_sym : symbol_table.symbols)
  {
    const symbolt &sym = name_sym.second;

    const std::string sym_name = id2string(sym.name);
    if(sym_name.compare(0, class_prefix.size(), class_prefix) != 0)
      continue;

    if(sym.type.id() != ID_cpp_declaration)
      continue;
    const cpp_declarationt &decl = to_cpp_declaration(sym.type);
    if(!decl.is_template())
      continue;
    if(decl.type().id() != "cpp-cast-operator")
      continue;
    if(decl.declarators().empty())
      continue;

    candidate_syms.push_back(&sym);
    candidate_scope_ids.push_back(sym.name);
  }

  if(candidate_syms.empty())
    return nullptr;

  // Phase 1: deduce-only pass.  For each candidate, run [temp.deduct.conv]/1
  // deduction and remember successful candidates.  Instantiation is
  // deferred until after partial ordering picks a unique winner, so
  // we don't pollute the symbol table with side-effects of losing
  // candidates.
  std::vector<conversion_deduction_resultt> survivors;
  std::vector<irep_idt> survivor_scope_ids; // parallel: F_scope_id per survivor
  for(std::size_t cand_i = 0; cand_i < candidate_syms.size(); ++cand_i)
  {
    const symbolt *cand_sym = candidate_syms[cand_i];
    const irep_idt &cand_name = candidate_scope_ids[cand_i];
    if(cand_sym == nullptr)
      continue;

    const cpp_declarationt cand_decl = to_cpp_declaration(cand_sym->type);
    const cpp_declaratort &declarator = cand_decl.declarators()[0];

    // P = return type of the conversion-function template per
    // [temp.deduct.conv]/1.  For a template cast operator, the
    // return type is stored in the second sub-element of the
    // declarator name (parsed from `operator <type-id>()`).  The
    // stored representation is unprocessed, with template
    // parameters embedded as cpp_names — exactly the input shape
    // `guess_template_args` expects.
    if(declarator.name().get_sub().size() < 2)
      continue;
    typet P = static_cast<const typet &>(declarator.name().get_sub()[1]);
    typet A = to;

    // The template cast operator's return type comes straight from
    // the parser, so its top-level reference may be encoded with
    // `ID_frontend_pointer` rather than `ID_pointer`.  Treat both as
    // references for the purposes of [temp.deduct.conv]/2.
    auto strip_top_reference = [](typet &t)
    {
      if(
        (t.id() == ID_pointer || t.id() == ID_frontend_pointer) &&
        t.get_bool(ID_C_reference))
      {
        t = static_cast<const typet &>(to_type_with_subtype(t).subtype());
      }
    };

    // [temp.deduct.conv]/2: P-reference -> use referred type.
    strip_top_reference(P);

    // [temp.deduct.conv]/4: A-reference -> use referred type.
    const bool A_was_reference =
      is_reference(A) ||
      (A.id() == ID_frontend_pointer && A.get_bool(ID_C_reference));
    strip_top_reference(A);

    // [temp.deduct.conv]/3: A non-reference -> P array→pointer,
    // function→pointer, drop top-level cv from P.
    if(!A_was_reference)
    {
      if(P.id() == ID_array)
      {
        const typet element = to_array_type(P).element_type();
        P = pointer_type(element);
      }
      else if(P.id() == ID_code)
      {
        P = pointer_type(P);
      }
      else
      {
        c_qualifierst pq;
        pq.read(P);
        if(pq.is_constant || pq.is_volatile || pq.is_restricted || pq.is_atomic)
        {
          c_qualifierst empty;
          empty.write(P);
        }
      }
    }

    // [temp.deduct.conv]/4 cont.: A cv-qualified -> drop top-level cv.
    {
      c_qualifierst aq;
      aq.read(A);
      if(aq.is_constant || aq.is_volatile || aq.is_restricted || aq.is_atomic)
      {
        c_qualifierst empty;
        empty.write(A);
      }
    }

    // SFINAE-guarded deduction per [temp.deduct]/8.
    cpp_save_scopet save_scope{cpp_scopes};
    cpp_saved_template_mapt saved_map{template_map};

    cpp_template_args_tct guessed_args;
    bool deduction_ok = false;

    try
    {
      sfinae_contextt sfinae_guard{*this};

      template_map.build_unassigned(cand_decl.template_type());

      // Move into the template's spec scope so cpp_name lookup
      // during deduction finds the template parameters.
      auto scope_it = cpp_scopes.id_map.find(cand_name);
      if(scope_it != cpp_scopes.id_map.end())
        cpp_scopes.go_to(static_cast<cpp_scopet &>(*scope_it->second));

      cpp_typecheck_resolvet resolver{*this};
      resolver.guess_template_args(P, A);

      guessed_args =
        template_map.build_template_args(cand_decl.template_type());

      if(!guessed_args.has_unassigned())
        deduction_ok = true;
    }
    catch(...)
    {
      // [temp.deduct]/8: SFINAE — substitution failure in the
      // immediate context is a deduction failure, not an error.
    }

    if(!deduction_ok)
      continue;

    conversion_deduction_resultt res;
    res.cand_sym = cand_sym;
    res.guessed_args = std::move(guessed_args);
    res.P_for_partial_ordering = P;
    survivors.push_back(std::move(res));
    survivor_scope_ids.push_back(cand_name);
  }

  if(survivors.empty())
    return nullptr;

  // Phase 2: [temp.deduct.partial]/3.2 + [over.match.best]/2.
  // Find the unique most-specialised survivor.
  std::size_t winner_idx = 0;
  if(survivors.size() > 1)
  {
    auto more_specialised_than = [&](std::size_t i, std::size_t j) -> bool
    {
      // i is more-specialised than j iff
      //   i at-least-as-specialised as j AND not (j at-least-as-
      //   specialised as i).
      const cpp_declarationt &Fi =
        to_cpp_declaration(survivors[i].cand_sym->type);
      const cpp_declarationt &Fj =
        to_cpp_declaration(survivors[j].cand_sym->type);
      const bool i_aas_j = conversion_template_at_least_as_specialised(
        Fi, Fj, survivor_scope_ids[i], survivor_scope_ids[j]);
      const bool j_aas_i = conversion_template_at_least_as_specialised(
        Fj, Fi, survivor_scope_ids[j], survivor_scope_ids[i]);
      return i_aas_j && !j_aas_i;
    };

    bool unique_winner = false;
    for(std::size_t i = 0; i < survivors.size(); ++i)
    {
      bool dominates_all = true;
      for(std::size_t j = 0; j < survivors.size(); ++j)
      {
        if(i == j)
          continue;
        if(!more_specialised_than(i, j))
        {
          dominates_all = false;
          break;
        }
      }
      if(dominates_all)
      {
        winner_idx = i;
        unique_winner = true;
        break;
      }
    }

    if(!unique_winner)
      return nullptr; // genuine ambiguity — no most-specialised candidate.
  }

  // Phase 3: instantiate the unique winner.
  const symbolt *cand_sym = survivors[winner_idx].cand_sym;
  cpp_template_args_tct guessed_args =
    std::move(survivors[winner_idx].guessed_args);

  const symbolt *instance = nullptr;
  try
  {
    sfinae_contextt sfinae_guard{*this};
    instance = &instantiate_template(
      expr.source_location(), *cand_sym, guessed_args, guessed_args);
  }
  catch(...)
  {
    return nullptr;
  }

  if(instance == nullptr)
    return nullptr;

  // The instantiated symbol's type is `code_typet` with one
  // implicit `this` parameter (a pointer).
  if(instance->type.id() != ID_code)
    return nullptr;
  const code_typet &inst_code = to_code_type(instance->type);
  if(inst_code.parameters().size() != 1)
    return nullptr;
  if(!inst_code.parameters().front().get_this())
    return nullptr;

  // Mark the instantiated cast-operator component (added to the
  // class's components vector by `instantiate_template` ->
  // `typecheck_compound_declarator`) so the non-template branches
  // of `user_defined_conversion_sequence` and `reference_binding`
  // skip it on subsequent calls.  Otherwise it would shadow a
  // fresh deduction for a different destination type
  // ([over.ics.user]/3 + [over.match.conv]).
  {
    symbolt *class_sym_w = symbol_table.get_writeable(class_id_with_tag);
    if(class_sym_w != nullptr && class_sym_w->type.id() == ID_struct)
    {
      struct_typet &cls_struct = to_struct_type(class_sym_w->type);
      for(auto &component : cls_struct.components())
      {
        if(component.get_name() == instance->name)
        {
          component.set("#is_template_specialization", true);
          break;
        }
      }
    }
  }

  return instance;
}

bool cpp_typecheckt::deduce_conversion_template(
  const exprt &expr,
  const typet &to,
  exprt &new_expr,
  unsigned &rank)
{
  const symbolt *instance = find_template_conversion_specialisation(expr, to);
  if(instance == nullptr)
    return false;

  const code_typet &inst_code = to_code_type(instance->type);

  // Build the conversion expression as a direct call to the
  // instantiated symbol.  We bypass the cpp_name-driven member-
  // call resolver because the freshly-instantiated cast operator,
  // although registered as a component of the source class by
  // `instantiate_template`, is *not* registered in the class
  // cpp_scope under a base_name lookup-friendly key.  Building the
  // call from `cpp_symbol_expr(*instance)` with the source object
  // as the implicit `this` argument is direct and avoids the
  // resolver.
  address_of_exprt this_arg{expr};
  this_arg.type() = inst_code.parameters().front().type();

  side_effect_expr_function_callt func_expr{
    cpp_symbol_expr(*instance),
    {this_arg},
    inst_code.return_type(),
    expr.source_location()};

  // [over.ics.user]/3: the second standard conversion sequence
  // shall have Exact Match rank.  In CBMC's encoding, Exact Match
  // adds zero rank (identity / qualification conversion).
  unsigned post_rank = 0;
  exprt post_expr;
  if(!standard_conversion_sequence(func_expr, to, post_expr, post_rank))
    return false;
  if(post_rank > 0)
    return false;

  rank += post_rank;
  new_expr.swap(post_expr);
  return true;
}

bool cpp_typecheckt::deduce_conversion_template_for_reference(
  const exprt &expr,
  const reference_typet &reference_type,
  exprt &new_expr,
  unsigned &rank)
{
  const symbolt *instance =
    find_template_conversion_specialisation(expr, reference_type);
  if(instance == nullptr)
    return false;

  const code_typet &inst_code = to_code_type(instance->type);

  // The cast operator must return a reference type for direct
  // reference binding ([over.match.ref]).
  if(!is_reference(inst_code.return_type()))
    return false;

  // Build the call as a direct symbol-driven function-call expr,
  // mirroring the value-target path.
  address_of_exprt this_arg{expr};
  this_arg.type() = inst_code.parameters().front().type();

  side_effect_expr_function_callt func_expr{
    cpp_symbol_expr(*instance),
    {this_arg},
    inst_code.return_type(),
    expr.source_location()};

  // The returned value of a reference-returning function is an
  // lvalue (the dereferenced pointer-to-reference).  Mirror the
  // shape that the non-template path in `reference_binding`
  // expects: take the address of the returned value via the
  // standard `add_implicit_dereference` plus reference_compatible
  // dance.  See the analogous block in `reference_binding`.
  exprt returned_value = func_expr;
  add_implicit_dereference(returned_value);

  unsigned ref_rank = 0;
  if(!returned_value.get_bool(ID_C_lvalue))
    return false;
  if(!reference_compatible(returned_value, reference_type, ref_rank))
    return false;

  // [over.ics.user]/3: when the user-defined conversion is by a
  // template specialisation the second standard conversion
  // sequence is required to have Exact Match rank.  For reference
  // binding the analogous requirement is that
  // `reference_compatible` succeed without adding any rank beyond
  // the identity (i.e., `ref_rank == 0`).
  if(ref_rank > 0)
    return false;

  // Returned values are lvalues only via references; the inner
  // operand is the pointer-to-reference whose dereference produced
  // the lvalue.
  if(returned_value.id() != ID_dereference)
    return false;
  if(!is_reference(to_dereference_expr(returned_value).op().type()))
    return false;

  exprt addr = to_multi_ary_expr(returned_value).op0();

  if(returned_value.type() != reference_type.base_type())
  {
    c_qualifierst qual_from;
    qual_from.read(returned_value.type());
    make_ptr_typecast(addr, reference_type);
    qual_from.write(to_reference_type(addr.type()).base_type());
  }

  // [over.ics.user] gives a user-defined conversion an extra rank
  // bump of 4 to dominate any standard conversion sequence; the
  // existing non-template reference-conversion path uses the same
  // constant.  Stay consistent with it.
  rank += 4 + ref_rank;
  new_expr.swap(addr);
  return true;
}

/// User-defined conversion sequence
/// \par parameters: A typechecked expression 'expr', a destination
/// type 'type'.
/// \return True iff a user-defined conversion sequence exists. The result of
///   the conversion is stored in 'new_expr'.
bool cpp_typecheckt::user_defined_conversion_sequence(
  const exprt &expr,
  const typet &to,
  exprt &new_expr,
  unsigned &rank)
{
  PRECONDITION(!is_reference(expr.type()));
  PRECONDITION(!is_reference(to));

  const typet &from = expr.type();

  new_expr.make_nil();

  // special case:
  // A conversion from a type to the same type is given an exact
  // match rank even though a user-defined conversion is used

  if(from == to)
    rank += 0;
  else
    rank += 4; // higher than all the standard conversions

  if(to.id() == ID_struct_tag)
  {
    // Ensure the target type is complete before looking for constructors.
    // For libc++ std::function, the type may be incomplete from a
    // forward declaration and needs elaboration.
    elaborate_class_template(to);

    std::string err_msg;

    if(cpp_is_pod(to))
    {
      if(from.id() == ID_struct_tag)
      {
        const struct_typet &from_struct = follow_tag(to_struct_tag_type(from));
        const struct_typet &to_struct = follow_tag(to_struct_tag_type(to));

        // potentially requires
        // expr.get_bool(ID_C_lvalue) ??

        if(subtype_typecast(from_struct, to_struct))
        {
          exprt address = address_of_exprt(expr);

          // simplify address
          if(expr.id() == ID_dereference)
            address = to_dereference_expr(expr).pointer();

          pointer_typet ptr_sub = pointer_type(to);
          c_qualifierst qual_from;
          qual_from.read(expr.type());
          qual_from.write(ptr_sub.base_type());
          make_ptr_typecast(address, ptr_sub);

          const dereference_exprt deref(address);

          // create temporary object
          side_effect_exprt tmp_object_expr(
            ID_temporary_object, to, expr.source_location());
          tmp_object_expr.copy_to_operands(deref);
          tmp_object_expr.set(ID_C_lvalue, true);
          tmp_object_expr.set(ID_mode, ID_cpp);

          new_expr.swap(tmp_object_expr);
          return true;
        }
      }
    }
    else
    {
      bool found = false;
      // Per [over.match.best]: when multiple converting
      // constructors are viable for a given source, pick the one
      // with the best conversion rank.  Ambiguity is only reported
      // when two or more candidates are *equally best*.  The
      // straightforward `found = true; if(found) return false;`
      // pattern below treats *any* second viable candidate as
      // ambiguous, which incorrectly rejects calls like
      // `power(2, size_t{})` on a class with overloaded
      // `BigInt(int)` / `BigInt(unsigned)` / `BigInt(long)` /
      // `BigInt(unsigned long)` constructors — the int argument
      // matches `BigInt(int)` exactly and should win unambiguously.
      // Track the best rank seen so far and the result expression
      // for the best candidate; flag ambiguity only on a tie.
      unsigned best_rank = 0;
      exprt best_expr = nil_exprt{};
      bool best_is_ambiguous = false;
      const auto &struct_type_to = follow_tag(to_struct_tag_type(to));

      for(const auto &component : struct_type_to.components())
      {
        if(component.get_bool(ID_from_base))
          continue;

        if(component.get_bool(ID_is_explicit))
          continue;

        const typet &comp_type = component.type();

        if(comp_type.id() != ID_code)
          continue;

        if(to_code_type(comp_type).return_type().id() != ID_constructor)
          continue;

        // TODO: ellipsis

        const auto &parameters = to_code_type(comp_type).parameters();

        // Accept constructors with exactly one real parameter (the
        // traditional single-arg converting constructor) OR
        // constructors where every parameter from position 2
        // onwards has a default value — i.e., still a single-arg
        // call site from the user's perspective.  Without this,
        // constructors like
        //   basic_string(const char*, const _Alloc& = _Alloc())
        // would be skipped even though they are the standard
        // conversion path for `const char*` / `char[N]` to
        // std::string.
        if(parameters.size() < 2)
          continue;
        bool all_extras_have_default = true;
        for(std::size_t pi = 2; pi < parameters.size(); ++pi)
        {
          if(!parameters[pi].has_default_value())
          {
            all_extras_have_default = false;
            break;
          }
        }
        if(!all_extras_have_default)
          continue;

        exprt curr_arg1 = parameters[1];
        typet arg1_type = curr_arg1.type();

        if(is_reference(arg1_type))
        {
          typet tmp = to_reference_type(arg1_type).base_type();
          arg1_type.swap(tmp);
        }

        unsigned tmp_rank = 0;
        if(arg1_type.id() != ID_struct_tag)
        {
          exprt tmp_expr;
          if(standard_conversion_sequence(expr, arg1_type, tmp_expr, tmp_rank))
          {
            if(expr.get_bool(ID_C_lvalue))
              tmp_expr.set(ID_C_lvalue, true);

            tmp_expr.add_source_location() = expr.source_location();

            exprt func_symb = cpp_symbol_expr(lookup(component.get_name()));
            func_symb.type() = comp_type;
            already_typechecked_exprt::make_already_typechecked(func_symb);

            // create temporary object
            side_effect_expr_function_callt ctor_expr(
              std::move(func_symb),
              {tmp_expr},
              uninitialized_typet{},
              expr.source_location());
            typecheck_side_effect_function_call(ctor_expr);
            CHECK_RETURN(ctor_expr.get(ID_statement) == ID_temporary_object);

            if(struct_type_to.get_bool(ID_C_constant))
              ctor_expr.type().set(ID_C_constant, true);

            // Track the best-ranked viable candidate per
            // [over.match.best].  A strictly lower rank replaces
            // the current best; an equal rank flags ambiguity.
            if(!found || tmp_rank < best_rank)
            {
              found = true;
              best_rank = tmp_rank;
              best_expr = std::move(ctor_expr);
              best_is_ambiguous = false;
            }
            else if(tmp_rank == best_rank)
            {
              best_is_ambiguous = true;
            }
          }
        }
        else if(from.id() == ID_struct_tag && arg1_type.id() == ID_struct_tag)
        {
          // try derived-to-base conversion
          //
          // Per [class.copy.ctor]/1 and [dcl.init]/14: copy-initialization
          // of an object of type `T` from an expression of type `T` (or
          // `const T`) uses the copy constructor.  When `from == arg1_type`
          // modulo cv-qualifiers, this is the SAME-TYPE copy-construction,
          // not derived-to-base.  The address-of + standard-conversion
          // path below would build `from* -> arg1*` via
          // `standard_conversion_sequence`, which DROPS const-qualifiers
          // on the pointee — that's not a valid implicit conversion
          // (per [conv.qual]) so the path silently rejects the
          // converting-ctor match for any `const T` source binding into a
          // `T` parameter.  This shows up in CBMC's own
          // `simplify_expr_*.cpp` files where simplification helpers
          // return `const exprt&` into a class-typed `resultt<>`
          // returned-value.  Fall through to the same-type path: strip
          // cv-qualifiers from `from` before computing the
          // address-of and let the standard-conversion sequence run on
          // the unqualified pointer types.  The conversion is still a
          // user-defined conversion (constructor call) so the rank
          // adjustment is unchanged.
          typet from_unqual = expr.type();
          from_unqual.remove(ID_C_constant);
          from_unqual.remove(ID_C_volatile);
          exprt expr_for_addr = expr;
          expr_for_addr.type() = from_unqual;
          address_of_exprt expr_pfrom(expr_for_addr, pointer_type(from_unqual));
          pointer_typet pto = pointer_type(arg1_type);

          exprt expr_ptmp;
          tmp_rank = 0;
          if(standard_conversion_sequence(expr_pfrom, pto, expr_ptmp, tmp_rank))
          {
            // create temporary object
            dereference_exprt expr_deref(expr_ptmp);
            // [basic.lval] p1, [expr.static.cast] p3: if the original
            // expression is an rvalue, the derived-to-base result is an
            // xvalue (not an lvalue), so it can bind to rvalue references.
            if(expr.get_bool(ID_C_lvalue))
              expr_deref.set(ID_C_lvalue, true);
            expr_deref.add_source_location() = expr.source_location();

            exprt new_object(ID_new_object, to);
            new_object.set(ID_C_lvalue, true);
            new_object.type().set(ID_C_constant, false);

            exprt func_symb = cpp_symbol_expr(lookup(component.get_name()));
            func_symb.type() = comp_type;
            already_typechecked_exprt::make_already_typechecked(func_symb);

            side_effect_expr_function_callt ctor_expr(
              std::move(func_symb),
              {expr_deref},
              uninitialized_typet{},
              expr.source_location());
            typecheck_side_effect_function_call(ctor_expr);

            INVARIANT(
              ctor_expr.get(ID_statement) == ID_temporary_object,
              "statement ID");

            if(struct_type_to.get_bool(ID_C_constant))
              ctor_expr.type().set(ID_C_constant, true);

            // Track best candidate as above.
            if(!found || tmp_rank < best_rank)
            {
              found = true;
              best_rank = tmp_rank;
              best_expr = std::move(ctor_expr);
              best_is_ambiguous = false;
            }
            else if(tmp_rank == best_rank)
            {
              best_is_ambiguous = true;
            }
          }
        }
      }
      // [over.match.best]: ambiguity is only an error when two or
      // more candidates are equally best.  If we found a unique
      // best, commit to it.
      if(found && best_is_ambiguous)
        return false;
      if(found)
      {
        new_expr.swap(best_expr);
        rank += best_rank;
        return true;
      }

      // No non-template converting constructor found. Try template
      // constructors via the full constructor resolution path, but
      // only if there are non-explicit template constructors.
      if(
        !in_template_conversion &&
        struct_type_to.get_bool("has_template_constructor"))
      {
        in_template_conversion = true;
        // [over.ics.user] + [temp.deduct]/8: a user-defined
        // conversion that instantiates a template constructor is
        // SFINAE-guarded — substitution failure means "no viable
        // conversion sequence", not a compilation error.  The
        // conversion is simply dropped from the candidate set.
        try
        {
          sfinae_contextt sfinae_guard{*this};
          exprt tmp_expr;
          exprt::operandst ops;
          ops.push_back(expr);
          new_temporary(expr.source_location(), to, ops, tmp_expr);
          in_template_conversion = false;
          // [class.conv.ctor]/2 + [over.match.copy]: only
          // non-explicit constructors participate in a user-
          // defined conversion sequence.  `new_temporary` runs
          // *direct*-initialisation semantics, which allow
          // explicit constructors — this is wrong for a UDCS.
          // Furthermore, a UDCS may use only standard conversions
          // for the constructor's argument; chaining a second
          // user-defined conversion ([over.best.ics]) is
          // forbidden.  Both errors manifest the same way: the
          // ctor selected by `new_temporary` is a non-template
          // explicit ctor that the regular loop above already
          // rejected.  The regular loop has already considered
          // every non-template, non-explicit converting ctor; if
          // it didn't find a match, the template fallback may
          // only legitimately succeed by selecting a *template*
          // specialisation.  Reject any non-template ctor here.
          //
          // Find the called ctor symbol inside `tmp_expr` and
          // check whether it carries `ID_specialization_of` (set
          // on template-instantiated symbols by
          // `cpp_typecheck_template.cpp:550`).
          std::function<const symbolt *(const exprt &)> find_ctor =
            [&](const exprt &e) -> const symbolt *
          {
            if(
              e.id() == ID_side_effect &&
              e.get(ID_statement) == ID_function_call)
            {
              const auto &fc = to_side_effect_expr_function_call(e);
              if(fc.function().id() == ID_symbol)
              {
                return symbol_table.lookup(
                  to_symbol_expr(fc.function()).get_identifier());
              }
            }
            for(const auto &op : e.operands())
            {
              if(const symbolt *r = find_ctor(op))
                return r;
            }
            const auto &init = e.find(ID_initializer);
            if(init.is_not_nil() && init.id() == ID_code)
            {
              if(const symbolt *r = find_ctor(static_cast<const exprt &>(init)))
                return r;
            }
            return nullptr;
          };
          const symbolt *ctor_sym = find_ctor(tmp_expr);
          if(
            ctor_sym != nullptr &&
            ctor_sym->type.find(ID_specialization_of).is_nil())
          {
            // Non-template ctor selected — the regular loop
            // either already rejected it or it is `explicit`.
            // Either way, this is not a valid user-defined
            // conversion.  Drop the result and continue to the
            // basic_string fallback / final `return false`.
          }
          else
          {
            new_expr.swap(tmp_expr);
            return true;
          }
        }
        catch(...)
        {
          in_template_conversion = false;
        }
      }

      // libstdc++ basic_string fallback: when both the regular and
      // template constructor paths fail, recognise the
      // char-array/char-pointer → basic_string<char> case and
      // synthesise a call to the 4-arg
      //   basic_string(const _CharT*, size_type, const _Alloc& = _Alloc())
      // constructor (basic_string.h:619), which is *not* template-
      // gated and is reliably present in the components list.  The
      // 3-arg
      //   basic_string(const _CharT*, const _Alloc& = _Alloc())
      // constructor (basic_string.h:641) is the natural conversion
      // path but is wrapped in a member template with a SFINAE
      // guard `template<typename = _RequireAllocator<_Alloc>>` —
      // CBMC's class elaboration fails to specialise the wrapper
      // in some translation-unit states (notably after
      // <bits/locale_classes.h> participates), and the constructor
      // disappears from the components list.
      //
      // This mirrors the workaround in `implicit_typecast` for
      // explicit casts; here we extend it to argument conversions
      // and reference bindings so calls like
      //   void f(const std::string&);  f("hello");
      // succeed regardless of the missing converting constructor.
      if(
        id2string(to_struct_tag_type(to).get_identifier())
          .find("tag-basic_string<") != std::string::npos)
      {
        const typet &src_t = expr.type();
        bool src_is_char_array =
          src_t.id() == ID_array &&
          (to_array_type(src_t).element_type().id() == ID_signedbv ||
           to_array_type(src_t).element_type().id() == ID_unsignedbv) &&
          to_bitvector_type(to_array_type(src_t).element_type()).get_width() ==
            config.ansi_c.char_width;
        bool src_is_char_ptr =
          src_t.id() == ID_pointer &&
          (to_pointer_type(src_t).base_type().id() == ID_signedbv ||
           to_pointer_type(src_t).base_type().id() == ID_unsignedbv) &&
          to_bitvector_type(to_pointer_type(src_t).base_type()).get_width() ==
            config.ansi_c.char_width;
        if(src_is_char_array || src_is_char_ptr)
        {
          exprt char_ptr = expr;
          if(src_is_char_array)
          {
            pointer_typet ptr_type =
              pointer_type(to_array_type(src_t).element_type());
            ptr_type.base_type().set(ID_C_constant, true);
            char_ptr = typecast_exprt(
              address_of_exprt(index_exprt(
                expr,
                from_integer(0, c_index_type()),
                to_array_type(src_t).element_type())),
              ptr_type);
          }
          // Determine the source string length: for a literal we
          // can compute it exactly; otherwise leave it
          // non-deterministic.
          exprt length_expr;
          if(
            char_ptr.id() == ID_typecast &&
            to_typecast_expr(char_ptr).op().id() == ID_address_of &&
            to_address_of_expr(to_typecast_expr(char_ptr).op()).object().id() ==
              ID_index &&
            to_index_expr(
              to_address_of_expr(to_typecast_expr(char_ptr).op()).object())
                .array()
                .id() == ID_string_constant)
          {
            const irep_idt &raw =
              to_string_constant(
                to_index_expr(
                  to_address_of_expr(to_typecast_expr(char_ptr).op()).object())
                  .array())
                .value();
            length_expr = from_integer(id2string(raw).size(), size_type());
          }
          else
          {
            length_expr =
              side_effect_expr_nondett{size_type(), expr.source_location()};
          }
          // Find the 4-arg `basic_string(const _CharT*, size_type,
          // const _Alloc& = _Alloc())` ctor in components.
          for(const auto &component : struct_type_to.components())
          {
            if(component.get_bool(ID_from_base))
              continue;
            const typet &comp_type = component.type();
            if(comp_type.id() != ID_code)
              continue;
            if(to_code_type(comp_type).return_type().id() != ID_constructor)
              continue;
            const auto &parameters = to_code_type(comp_type).parameters();
            if(parameters.size() != 4)
              continue;
            const typet &p1 = parameters[1].type();
            if(p1.id() != ID_pointer)
              continue;
            const typet &p1_base = to_pointer_type(p1).base_type();
            if(p1_base.id() != ID_signedbv && p1_base.id() != ID_unsignedbv)
              continue;
            const typet &p2 = parameters[2].type();
            if(p2.id() != ID_unsignedbv && p2.id() != ID_signedbv)
              continue;
            // Build the constructor call.
            exprt func_symb = cpp_symbol_expr(lookup(component.get_name()));
            func_symb.type() = comp_type;
            already_typechecked_exprt::make_already_typechecked(func_symb);
            side_effect_expr_function_callt ctor_expr(
              std::move(func_symb),
              {char_ptr, length_expr},
              uninitialized_typet{},
              expr.source_location());
            try
            {
              typecheck_side_effect_function_call(ctor_expr);
              if(ctor_expr.get(ID_statement) == ID_temporary_object)
              {
                new_expr.swap(ctor_expr);
                return true;
              }
            }
            catch(...)
            {
              // Fall through; conversion fails as before.
            }
            break;
          }
        }
      }
    }
  }

  // conversion operators
  if(from.id() == ID_struct_tag)
  {
    bool found = false;
    for(const auto &component :
        follow_tag(to_struct_tag_type(from)).components())
    {
      // Per [class.conv.fct]/1 + [class.member.lookup]/4: the set
      // of viable conversion operators in `from`'s class scope
      // includes those declared in `from` itself AND those
      // inherited from base classes (subject to access
      // resolution and potentially `using`-declaration hiding).
      // Don't filter out `from_base` components here — that
      // mirrors the standard's name-lookup rule.  Without this,
      // an inherited `operator T()` (e.g. `operator bool()`
      // inherited from `integral_constant<bool, V>` into
      // `__and_<...>`) is silently invisible to
      // user-defined-conversion search and the call site fails
      // with "invalid implicit conversion from 'struct __and_'
      // to 'bool'".

      if(!component.get_bool(ID_is_cast_operator))
        continue;

      // Skip cast operators that originated from a template
      // specialisation: per [over.match.conv] the candidate set
      // for a given destination type is the *non-template* cast
      // operators plus freshly-deduced specialisations.  A
      // specialisation that exists only because an *earlier*
      // user-defined conversion already deduced and instantiated
      // it must not shadow a fresh deduction for a different
      // destination type.  Mark applied below in
      // `deduce_conversion_template`.
      if(component.get_bool("#is_template_specialization"))
        continue;

      const code_typet &comp_type = to_code_type(component.type());
      DATA_INVARIANT(
        comp_type.parameters().size() == 1, "expected exactly one parameter");

      typet this_type = comp_type.parameters().front().type();
      this_type.set(ID_C_reference, true);

      exprt this_expr(expr);
      this_type.set(ID_C_this, true);

      unsigned tmp_rank = 0;
      exprt tmp_expr;

      if(implicit_conversion_sequence(this_expr, this_type, tmp_expr, tmp_rank))
      {
        // To take care of the possible virtual case,
        // we build the function as a member expression.
        const cpp_namet cpp_func_name(component.get_base_name());

        exprt member_func(ID_member);
        member_func.add(ID_component_cpp_name) = cpp_func_name;
        member_func.copy_to_operands(already_typechecked_exprt{expr});

        side_effect_expr_function_callt func_expr(
          std::move(member_func),
          {},
          uninitialized_typet{},
          expr.source_location());
        typecheck_side_effect_function_call(func_expr);

        if(standard_conversion_sequence(func_expr, to, tmp_expr, tmp_rank))
        {
          // check if it's ambiguous
          if(found)
            return false;
          found = true;

          rank += tmp_rank;
          new_expr.swap(tmp_expr);
        }
      }
    }
    if(found)
      return true;

    // No non-template cast operator matched.  If the source class
    // has template conversion operators, try [temp.deduct.conv]/1
    // deduction against the destination type.
    {
      unsigned tmpl_rank = 0;
      exprt tmpl_expr;
      if(deduce_conversion_template(expr, to, tmpl_expr, tmpl_rank))
      {
        rank += tmpl_rank;
        new_expr.swap(tmpl_expr);
        return true;
      }
    }
  }

  return new_expr.is_not_nil();
}

/// Reference-related
/// \par parameters: A typechecked expression 'expr',
/// a reference 'type'.
/// \return True iff the reference 'type' is reference-related to 'expr'.
bool cpp_typecheckt::reference_related(
  const exprt &expr,
  const reference_typet &reference_type) const
{
  PRECONDITION(!is_reference(expr.type()));

  const typet &from = expr.type();
  const typet &from_followed =
    from.id() == ID_struct_tag
      ? static_cast<const typet &>(follow_tag(to_struct_tag_type(from)))
    : from.id() == ID_union_tag
      ? static_cast<const typet &>(follow_tag(to_union_tag_type(from)))
      : from;
  const typet &to = reference_type.base_type();
  const typet &to_followed =
    to.id() == ID_struct_tag
      ? static_cast<const typet &>(follow_tag(to_struct_tag_type(to)))
    : to.id() == ID_union_tag
      ? static_cast<const typet &>(follow_tag(to_union_tag_type(to)))
      : to;

  // need to check #c_type
  if(from_followed.get(ID_C_c_type) != to_followed.get(ID_C_c_type))
    return false;

  if(from == to)
    return true;

  if(from.id() == ID_struct_tag && to.id() == ID_struct_tag)
  {
    const auto &from_s = to_struct_type(from_followed);
    const auto &to_s = to_struct_type(to_followed);
    return subtype_typecast(from_s, to_s) &&
           base_publicly_accessible(from_s, to_s);
  }

  if(
    from.id() == ID_struct_tag && reference_type.get_bool(ID_C_this) &&
    to.id() == ID_empty)
  {
    // virtual-call case
    return true;
  }

  return false;
}

/// Reference-compatible
/// \par parameters: A typechecked expression 'expr', a
/// reference 'type'.
/// \return True iff an the reference 'type' is reference-compatible to 'expr'.
bool cpp_typecheckt::reference_compatible(
  const exprt &expr,
  const reference_typet &reference_type,
  unsigned &rank) const
{
  PRECONDITION(!is_reference(expr.type()));

  if(!reference_related(expr, reference_type))
    return false;

  if(expr.type() != reference_type.base_type())
    rank += 3;

  c_qualifierst qual_from;
  qual_from.read(expr.type());

  c_qualifierst qual_to;
  qual_to.read(reference_type.base_type());

  if(qual_from != qual_to)
    rank += 1;

  if(qual_from.is_subset_of(qual_to))
    return true;

  return false;
}

/// Reference binding
///
/// When a parameter of reference type binds directly (8.5.3) to an
/// argument expression, the implicit conversion sequence is the
/// identity conversion, unless the argument expression has a type
/// that is a derived class of the parameter type, in which case the
/// implicit conversion sequence is a derived-to-base Conversion
/// (13.3.3.1).
///
/// If the parameter binds directly to the result of applying a
/// conversion function to the argument expression, the implicit
/// conversion sequence is a user-defined conversion sequence
/// (13.3.3.1.2), with the second standard conversion sequence
/// either an identity conversion or, if the conversion function
/// returns an entity of a type that is a derived class of the
/// parameter type, a derived-to-base Conversion.
///
/// When a parameter of reference type is not bound directly to
/// an argument expression, the conversion sequence is the one
/// required to convert the argument expression to the underlying
/// type of the reference according to 13.3.3.1. Conceptually, this
/// conversion sequence corresponds to copy-initializing a temporary
/// of the underlying type with the argument expression. Any
/// difference in top-level cv-qualification is subsumed by the
/// initialization itself and does not constitute a conversion.
///
/// A standard conversion sequence cannot be formed if it requires
/// binding a reference to non-const to an rvalue (except when
/// binding an implicit object parameter; see the special rules
/// for that case in 13.3.1).
/// \par parameters: A typechecked expression 'expr', a
/// reference 'type'.
/// \return True iff an the reference can be bound to the expression. The result
///   of the conversion is stored in 'new_expr'.
bool cpp_typecheckt::reference_binding(
  exprt expr,
  const reference_typet &reference_type,
  exprt &new_expr,
  unsigned &rank)
{
  PRECONDITION(!is_reference(expr.type()));

  unsigned backup_rank = rank;

  if(reference_type.get_bool(ID_C_this) && !expr.get_bool(ID_C_lvalue))
  {
    // `this' has to be an lvalue
    if(expr.get(ID_statement) == ID_temporary_object)
      expr.set(ID_C_lvalue, true);
    else if(expr.get(ID_statement) == ID_function_call)
      expr.set(ID_C_lvalue, true);
    else if(expr.get_bool(ID_C_temporary_avoided))
    {
      expr.remove(ID_C_temporary_avoided);
      exprt temporary;
      new_temporary(expr.source_location(), expr.type(), expr, temporary);
      expr.swap(temporary);
      expr.set(ID_C_lvalue, true);
    }
    else
      return false;
  }

  // C++11: rvalue references cannot bind to lvalues.
  // Temporaries are internally marked as lvalues but are rvalues in C++.
  // Also, implicit dereferences of rvalue references are xvalues, not lvalues,
  // but only when the rvalue reference is unnamed (e.g., from static_cast or
  // function return). Named rvalue reference variables are lvalues.
  if(
    is_rvalue_reference(reference_type) && expr.get_bool(ID_C_lvalue) &&
    expr.get(ID_statement) != ID_temporary_object &&
    !(expr.id() == ID_dereference && expr.get_bool(ID_C_implicit) &&
      ((is_rvalue_reference(to_dereference_expr(expr).pointer().type()) &&
        to_dereference_expr(expr).pointer().id() != ID_symbol) ||
       (to_dereference_expr(expr).pointer().id() == ID_address_of &&
        to_address_of_expr(to_dereference_expr(expr).pointer())
            .object()
            .get(ID_statement) == ID_temporary_object))))
  {
    // C++11: const lvalues can bind to T&& through a temporary copy.
    // Create a temporary and bind the rvalue reference to it.
    typet base = reference_type.base_type();
    base.remove(ID_C_constant);
    typet expr_base = expr.type();
    expr_base.remove(ID_C_constant);
    if(base == expr_base)
    {
      exprt tmp = expr;
      tmp.remove(ID_C_lvalue);
      tmp.set(ID_statement, ID_temporary_object);
      if(reference_compatible(tmp, reference_type, rank))
      {
        new_expr = tmp;
        rank += 4;
        return true;
      }
    }
    return false;
  }

  // C++11: xvalues (implicit dereferences of rvalue references) cannot
  // bind to non-const lvalue references. Named rvalue reference variables
  // are lvalues, so only reject unnamed rvalue references (e.g., from
  // static_cast or function return values).
  //
  // Exception: the implicit object parameter of a member function call
  // (`reference_type.get_bool(ID_C_this)`) is special — it is not a
  // user-visible lvalue reference parameter but the result of CBMC's
  // internal pointer-to-`this`-as-reference conversion.  An xvalue
  // receiver (e.g. `std::move(*this).method()`) must be allowed to
  // bind to it for `&&`-qualified member functions to be callable at
  // all.  Without this exception, every `std::move(receiver).method()`
  // fails overload resolution because the candidate's implicit `this`
  // is interpreted as a non-const lvalue ref.
  if(
    !is_rvalue_reference(reference_type) &&
    !reference_type.base_type().get_bool(ID_C_constant) &&
    !reference_type.get_bool(ID_C_this) && expr.id() == ID_dereference &&
    expr.get_bool(ID_C_implicit) &&
    is_rvalue_reference(to_dereference_expr(expr).pointer().type()) &&
    to_dereference_expr(expr).pointer().id() != ID_symbol)
    return false;

  if(
    expr.get_bool(ID_C_lvalue) ||
    reference_type.base_type().get_bool(ID_C_constant) ||
    is_rvalue_reference(reference_type))
  {
    if(reference_compatible(expr, reference_type, rank))
    {
      if(!expr.get_bool(ID_C_lvalue))
      {
        // create temporary object
        side_effect_exprt tmp{
          ID_temporary_object,
          {std::move(expr)},
          reference_type.base_type(),
          expr.source_location()};
        tmp.set(ID_mode, ID_cpp);
        expr.swap(tmp);
      }

      {
        address_of_exprt tmp(expr, ::reference_type(expr.type()));
        tmp.add_source_location() = expr.source_location();
        new_expr.swap(tmp);
      }

      if(expr.type() != reference_type.base_type())
      {
        c_qualifierst qual_from;
        qual_from.read(expr.type());
        if(
          expr.type().id() == ID_struct_tag &&
          reference_type.base_type().id() == ID_struct_tag)
        {
          make_ptr_typecast(new_expr, reference_type);
        }
        else
        {
          new_expr = typecast_exprt::conditional_cast(new_expr, reference_type);
        }
        qual_from.write(to_reference_type(new_expr.type()).base_type());
      }

      return true;
    }

    rank = backup_rank;
  }

  // conversion operators
  if(expr.type().id() == ID_struct_tag)
  {
    for(const auto &component :
        follow_tag(to_struct_tag_type(expr.type())).components())
    {
      if(component.get_bool(ID_from_base))
        continue;

      if(!component.get_bool(ID_is_cast_operator))
        continue;

      // Skip components that are template-conversion-operator
      // specialisations from a previous deduction; their
      // counterpart for *this* destination type (which may be a
      // different reference) is found below by
      // `deduce_conversion_template_for_reference`.
      // ([over.ics.user]/3 + [over.match.conv])
      if(component.get_bool("#is_template_specialization"))
        continue;

      const code_typet &component_type = to_code_type(component.type());

      // otherwise it cannot bind directly (not an lvalue)
      if(!is_reference(component_type.return_type()))
        continue;

      DATA_INVARIANT(
        component_type.parameters().size() == 1, "exactly one parameter");

      typet this_type = component_type.parameters().front().type();
      this_type.set(ID_C_reference, true);

      exprt this_expr(expr);

      this_type.set(ID_C_this, true);

      unsigned tmp_rank = 0;

      exprt tmp_expr;
      if(implicit_conversion_sequence(this_expr, this_type, tmp_expr, tmp_rank))
      {
        // To take care of the possible virtual case,
        // we build the function as a member expression.
        const cpp_namet cpp_func_name(component.get_base_name());

        exprt member_func(ID_member);
        member_func.add(ID_component_cpp_name) = cpp_func_name;
        member_func.copy_to_operands(already_typechecked_exprt{expr});

        side_effect_expr_function_callt func_expr(
          std::move(member_func),
          {},
          uninitialized_typet{},
          expr.source_location());
        typecheck_side_effect_function_call(func_expr);

        // let's check if the returned value binds directly
        exprt returned_value = func_expr;
        add_implicit_dereference(returned_value);

        if(
          returned_value.get_bool(ID_C_lvalue) &&
          reference_compatible(returned_value, reference_type, rank))
        {
          // returned values are lvalues in case of references only
          DATA_INVARIANT(
            is_reference(to_dereference_expr(returned_value).op().type()),
            "the returned value must be pointer to reference");

          new_expr = to_multi_ary_expr(returned_value).op0();

          if(returned_value.type() != reference_type.base_type())
          {
            c_qualifierst qual_from;
            qual_from.read(returned_value.type());
            make_ptr_typecast(new_expr, reference_type);
            qual_from.write(to_reference_type(new_expr.type()).base_type());
          }
          rank += 4 + tmp_rank;
          return true;
        }
      }
    }

    // No non-template reference-returning cast operator matched.
    // Per [temp.deduct.conv]/1 + [over.match.ref], try template
    // conversion-function specialisations whose return type
    // (after [temp.deduct.conv]/2 reference-stripping) deduces a
    // reference-compatible match against `reference_type`.
    {
      unsigned tmpl_rank = 0;
      exprt tmpl_expr;
      if(deduce_conversion_template_for_reference(
           expr, reference_type, tmpl_expr, tmpl_rank))
      {
        rank += tmpl_rank;
        new_expr.swap(tmpl_expr);
        return true;
      }
    }
  }

  // No temporary allowed for `this'
  if(reference_type.get_bool(ID_C_this))
    return false;

  if(
    !reference_type.base_type().get_bool(ID_C_constant) ||
    reference_type.base_type().get_bool(ID_C_volatile))
    return false;

  // TODO: handle the case for implicit parameters
  if(
    !reference_type.base_type().get_bool(ID_C_constant) &&
    !expr.get_bool(ID_C_lvalue))
    return false;

  exprt arg_expr = expr;

  if(arg_expr.type().id() == ID_struct_tag)
  {
    // required to initialize the temporary
    arg_expr.set(ID_C_lvalue, true);
  }

  if(user_defined_conversion_sequence(
       arg_expr, reference_type.base_type(), new_expr, rank))
  {
    address_of_exprt tmp(new_expr, ::reference_type(new_expr.type()));
    tmp.add_source_location() = new_expr.source_location();
    new_expr.swap(tmp);
    return true;
  }

  rank = backup_rank;
  if(standard_conversion_sequence(
       expr, reference_type.base_type(), new_expr, rank))
  {
    {
      // create temporary object
      side_effect_exprt tmp(
        ID_temporary_object,
        reference_type.base_type(),
        expr.source_location());
      tmp.set(ID_mode, ID_cpp);
      // tmp.set(ID_C_lvalue, true);
      tmp.add_to_operands(std::move(new_expr));
      new_expr.swap(tmp);
    }

    address_of_exprt tmp(new_expr, pointer_type(new_expr.type()));
    tmp.type().set(ID_C_reference, true);
    tmp.add_source_location() = new_expr.source_location();

    new_expr = tmp;
    return true;
  }

  return false;
}

/// implicit conversion sequence
/// \par parameters: A typechecked expression 'expr', a destination
/// type 'type'.
/// \return True iff an implicit conversion sequence exists. The result of the
///   conversion is stored in 'new_expr'. The rank of the sequence is stored in
///   'rank'
bool cpp_typecheckt::implicit_conversion_sequence(
  const exprt &expr,
  const typet &type,
  exprt &new_expr,
  unsigned &rank)
{
  unsigned backup_rank = rank;

  exprt e = expr;
  add_implicit_dereference(e);

  if(is_reference(type))
  {
    if(!reference_binding(e, to_reference_type(type), new_expr, rank))
      return false;

#if 0
    simplify_exprt simplify(*this);
    simplify.simplify(new_expr);
    new_expr.type().set(ID_C_reference, true);
#endif
  }
  else if(!standard_conversion_sequence(e, type, new_expr, rank))
  {
    rank = backup_rank;
    if(!user_defined_conversion_sequence(e, type, new_expr, rank))
    {
      if(
        type.id() == ID_integer &&
        (expr.type().id() == ID_signedbv || expr.type().id() == ID_unsignedbv))
      {
        // This is a nonstandard implicit conversion, from
        // bit-vectors to unbounded integers.
        rank = 0;
        new_expr = typecast_exprt(expr, type);
        return true;
      }
      else if(
        (type.id() == ID_signedbv || type.id() == ID_unsignedbv) &&
        expr.type().id() == ID_integer)
      {
        // This is a nonstandard implicit conversion, from
        // unbounded integers to bit-vectors.
        rank = 0;
        new_expr = typecast_exprt(expr, type);
        return true;
      }

      // no conversion
      return false;
    }

#if 0
    simplify_exprt simplify(*this);
    simplify.simplify(new_expr);
#endif
  }

  return true;
}

/// implicit conversion sequence
/// \par parameters: A typechecked expression 'expr', a destination
/// type 'type'.
/// \return True iff an implicit conversion sequence exists. The result of the
///   conversion is stored in 'new_expr'.
bool cpp_typecheckt::implicit_conversion_sequence(
  const exprt &expr,
  const typet &type,
  exprt &new_expr)
{
  unsigned rank = 0;
  return implicit_conversion_sequence(expr, type, new_expr, rank);
}

/// implicit conversion sequence
/// \par parameters: A typechecked expression 'expr', a destination
/// type 'type'.
/// \return True iff an implicit conversion sequence exists. The rank of the
///   sequence is stored in 'rank'
bool cpp_typecheckt::implicit_conversion_sequence(
  const exprt &expr,
  const typet &type,
  unsigned &rank)
{
  exprt new_expr;
  return implicit_conversion_sequence(expr, type, new_expr, rank);
}

void cpp_typecheckt::implicit_typecast(exprt &expr, const typet &type)
{
  const exprt orig_expr = expr;
  exprt e = expr;

  if(
    e.id() == ID_initializer_list && cpp_is_pod(type) &&
    e.operands().size() == 1)
  {
    e = to_unary_expr(expr).op();
  }

  if(!implicit_conversion_sequence(e, type, expr))
  {
    // Fallback: if the source is a char array (a string literal
    // after C++17 array-to-pointer decay) and the target is a
    // basic_string struct, try converting the source to `const
    // char*` first and retry.  libstdc++'s
    //   basic_string(const _CharT* __s, const _Alloc& __a = _Alloc())
    // constructor (basic_string.h line 641) is wrapped in a member
    // template with a SFINAE guard
    //   template<typename = _RequireAllocator<_Alloc>>
    // and is therefore not present in the struct's components
    // list.  The other `const char*` constructor,
    //   basic_string(const _CharT*, size_type, const _Alloc& = _Alloc())
    // requires an explicit size argument and is therefore unusable
    // for a plain `std::string = "hello"` initializer.
    //
    // Rather than teach the general conversion-sequence logic to
    // enumerate member-template constructors (an architectural
    // change), recognise this specific pattern and emit the
    // explicit `basic_string(const char*, size_type, Alloc())`
    // constructor call using strlen to compute the size.
    if(
      type.id() == ID_struct_tag &&
      id2string(to_struct_tag_type(type).get_identifier())
          .find("tag-basic_string<") != std::string::npos)
    {
      typet src_t = e.type();
      bool src_is_char_array =
        src_t.id() == ID_array &&
        (to_array_type(src_t).element_type().id() == ID_signedbv ||
         to_array_type(src_t).element_type().id() == ID_unsignedbv) &&
        to_bitvector_type(to_array_type(src_t).element_type()).get_width() ==
          config.ansi_c.char_width;
      bool src_is_char_ptr =
        src_t.id() == ID_pointer &&
        (to_pointer_type(src_t).base_type().id() == ID_signedbv ||
         to_pointer_type(src_t).base_type().id() == ID_unsignedbv) &&
        to_bitvector_type(to_pointer_type(src_t).base_type()).get_width() ==
          config.ansi_c.char_width;
      if(src_is_char_array || src_is_char_ptr)
      {
        // Decay array to pointer if needed.
        exprt char_ptr = e;
        if(src_is_char_array)
        {
          pointer_typet ptr_type =
            pointer_type(to_array_type(src_t).element_type());
          ptr_type.base_type().set(ID_C_constant, true);
          char_ptr = typecast_exprt(
            address_of_exprt(index_exprt(
              e,
              from_integer(0, c_index_type()),
              to_array_type(src_t).element_type())),
            ptr_type);
        }
        // Use strlen-style length: front end's __builtin_strlen is
        // recognised by CBMC.  Fall back to a nondet size if the
        // char_ptr is a non-constant expression.
        exprt length_expr;
        if(
          char_ptr.id() == ID_typecast &&
          to_typecast_expr(char_ptr).op().id() == ID_address_of &&
          to_address_of_expr(to_typecast_expr(char_ptr).op()).object().id() ==
            ID_index &&
          to_index_expr(
            to_address_of_expr(to_typecast_expr(char_ptr).op()).object())
              .array()
              .id() == ID_string_constant)
        {
          const irep_idt &raw =
            to_string_constant(
              to_index_expr(
                to_address_of_expr(to_typecast_expr(char_ptr).op()).object())
                .array())
              .value();
          length_expr = from_integer(id2string(raw).size(), size_type());
        }
        else
        {
          length_expr =
            side_effect_expr_nondett{size_type(), e.source_location()};
        }
        // Find `basic_string(const _CharT*, size_type, const _Alloc&)`.
        const struct_typet &struct_type_to =
          follow_tag(to_struct_tag_type(type));
        for(const auto &component : struct_type_to.components())
        {
          if(component.get_bool(ID_from_base))
            continue;
          const typet &comp_type = component.type();
          if(comp_type.id() != ID_code)
            continue;
          if(to_code_type(comp_type).return_type().id() != ID_constructor)
            continue;
          const auto &parameters = to_code_type(comp_type).parameters();
          // Look for (this, const char*, size_type, const Alloc&=...)
          if(parameters.size() != 4)
            continue;
          const typet &p1 = parameters[1].type();
          if(p1.id() != ID_pointer)
            continue;
          const typet &p1_base = to_pointer_type(p1).base_type();
          if(p1_base.id() != ID_signedbv && p1_base.id() != ID_unsignedbv)
            continue;
          const typet &p2 = parameters[2].type();
          if(p2.id() != ID_unsignedbv && p2.id() != ID_signedbv)
            continue;
          // Build the constructor call.
          exprt func_symb = cpp_symbol_expr(lookup(component.get_name()));
          func_symb.type() = comp_type;
          already_typechecked_exprt::make_already_typechecked(func_symb);
          side_effect_expr_function_callt ctor_expr(
            std::move(func_symb),
            {char_ptr, length_expr},
            uninitialized_typet{},
            e.source_location());
          try
          {
            typecheck_side_effect_function_call(ctor_expr);
            if(ctor_expr.get(ID_statement) == ID_temporary_object)
            {
              expr = std::move(ctor_expr);
              return;
            }
          }
          catch(...)
          {
            // fall through to the standard error below
          }
          break;
        }
      }
    }

    // Empty brace-init {} to pointer type: produces null pointer.
    // Used by MSVC's <exception> header: void* ptr = {};
    if(
      orig_expr.id() == ID_initializer_list && orig_expr.operands().empty() &&
      type.id() == ID_pointer && !is_reference(type))
    {
      expr = null_pointer_exprt(to_pointer_type(type));
      return;
    }

    // C++11 [dcl.init.list]/3: list-initialization with an empty
    // brace-init list `{}` value-initializes the destination.
    // For a class type (or reference to a class type) with an
    // accessible default constructor, this synthesises a default-
    // constructed temporary; for a reference target the caller
    // binds the reference via the address of the temporary.
    //
    // The match in `cpp_typecheck_fargst::match` (via
    // `brace_init_is_viable`) accepts `{}` as a viable conversion
    // for class types and class-reference types; this branch
    // performs the corresponding actual conversion so the
    // overall implicit-typecast succeeds rather than reaching
    // the "invalid implicit conversion" error path below.
    if(
      orig_expr.id() == ID_initializer_list && orig_expr.operands().empty() &&
      (type.id() == ID_struct_tag || type.id() == ID_struct ||
       (type.id() == ID_pointer && is_reference(type))))
    {
      typet base_type = type;
      bool target_is_reference = false;
      if(type.id() == ID_pointer && is_reference(type))
      {
        base_type = to_reference_type(type).base_type();
        target_is_reference = true;
      }
      if(base_type.id() == ID_struct_tag || base_type.id() == ID_struct)
      {
        // Skip std::initializer_list itself — the dedicated
        // brace-to-initializer_list block below handles those.
        const std::string base_id_str =
          base_type.id() == ID_struct_tag
            ? id2string(to_struct_tag_type(base_type).get_identifier())
            : std::string{};
        if(base_id_str.find("tag-initializer_list<") == std::string::npos)
        {
          try
          {
            // Default-construct via cpp_constructor on a marker
            // new_object so any user-defined default ctor (or the
            // POD zero-init path) is honoured uniformly.
            exprt temp;
            new_temporary(
              orig_expr.source_location(), base_type, exprt::operandst{}, temp);
            if(target_is_reference)
            {
              address_of_exprt addr{temp, pointer_type(base_type)};
              addr.type().set(ID_C_reference, true);
              if(is_rvalue_reference(type))
                addr.type().set(ID_C_rvalue_reference, true);
              expr = std::move(addr);
            }
            else
            {
              expr = std::move(temp);
            }
            return;
          }
          catch(...)
          {
            // Fall through to standard error path.
          }
        }
      }
    }

    // C++11 [dcl.init.list]/3.5: non-empty brace-init list to a
    // class (or reference-to-class) type with an accessible
    // `initializer_list<U>` constructor.
    //
    // Algorithm:
    //   1. Locate the `initializer_list<U>` ctor on the class and
    //      extract `U`.
    //   2. Recurse via `implicit_typecast` to materialise the
    //      brace-init as a value of type `std::initializer_list<U>`
    //      (handled by the existing brace-to-initializer_list block
    //      below — that block produces a `struct_exprt` of the
    //      `tag-initializer_list<U>` struct).
    //   3. Mark the synthesised initializer_list value as
    //      `already_typechecked` so that `cpp_constructor`'s
    //      argument-typecheck step doesn't reject it as
    //      `unexpected expression: struct`.
    //   4. Call `new_temporary` to construct the destination class
    //      temporary with the initializer_list as its argument.
    //   5. For a reference-typed target, bind the reference via
    //      `address_of` of the temporary.
    if(
      orig_expr.id() == ID_initializer_list && !orig_expr.operands().empty() &&
      (type.id() == ID_struct_tag || type.id() == ID_struct ||
       (type.id() == ID_pointer && is_reference(type))))
    {
      typet base_type = type;
      bool target_is_reference = false;
      if(type.id() == ID_pointer && is_reference(type))
      {
        base_type = to_reference_type(type).base_type();
        target_is_reference = true;
      }
      if(base_type.id() == ID_struct_tag || base_type.id() == ID_struct)
      {
        const std::string base_id_str =
          base_type.id() == ID_struct_tag
            ? id2string(to_struct_tag_type(base_type).get_identifier())
            : std::string{};
        // Skip std::initializer_list itself — the dedicated
        // brace-to-initializer_list block below handles those.
        if(base_id_str.find("tag-initializer_list<") == std::string::npos)
        {
          const struct_typet &class_type =
            base_type.id() == ID_struct_tag
              ? follow_tag(to_struct_tag_type(base_type))
              : to_struct_type(base_type);
          // Locate `initializer_list<U>` ctor and extract U.
          typet init_list_param_type;
          bool found_il_ctor = false;
          for(const auto &c : class_type.components())
          {
            if(c.type().id() != ID_code)
              continue;
            if(to_code_type(c.type()).return_type().id() != ID_constructor)
              continue;
            if(c.get_bool(ID_is_explicit))
              continue;
            const auto &params = to_code_type(c.type()).parameters();
            if(params.size() < 2)
              continue;
            typet p1_type = params[1].type();
            if(is_reference(p1_type))
              p1_type = to_reference_type(p1_type).base_type();
            if(p1_type.id() != ID_struct_tag)
              continue;
            if(
              id2string(to_struct_tag_type(p1_type).get_identifier())
                .find("tag-initializer_list<") == std::string::npos)
              continue;
            bool all_extras_default = true;
            for(std::size_t i = 2; i < params.size(); ++i)
            {
              if(!params[i].has_default_value())
              {
                all_extras_default = false;
                break;
              }
            }
            if(!all_extras_default)
              continue;
            init_list_param_type = p1_type;
            found_il_ctor = true;
            break;
          }
          if(found_il_ctor)
          {
            try
            {
              // Recurse: convert the brace-init to
              // std::initializer_list<U>.  This dispatches to
              // the existing brace-to-initializer_list handler
              // below, which produces a `struct_exprt` of the
              // initializer-list struct.
              exprt init_list_value = orig_expr;
              implicit_typecast(init_list_value, init_list_param_type);
              // Mark it as already typechecked so that
              // `cpp_constructor`'s `typecheck_expr(op)` call on
              // the argument does not re-traverse into the raw
              // `struct_exprt` (which would trip the
              // "unexpected expression: struct" path in
              // `c_typecheck_baset::typecheck_expr_main`).
              already_typechecked_exprt::make_already_typechecked(
                init_list_value);
              exprt temp;
              new_temporary(
                orig_expr.source_location(), base_type, init_list_value, temp);
              if(target_is_reference)
              {
                address_of_exprt addr{temp, pointer_type(base_type)};
                addr.type().set(ID_C_reference, true);
                if(is_rvalue_reference(type))
                  addr.type().set(ID_C_rvalue_reference, true);
                expr = std::move(addr);
              }
              else
              {
                expr = std::move(temp);
              }
              return;
            }
            catch(...)
            {
              // Fall through to the standard error path.
            }
          }
        }
      }
    }

    // Brace-init {a, b, ...} to aggregate struct: assign members
    // in order. Used by MSVC's <ratio> _Big_multiply return statement.
    //
    // Skip type-alias components (`first_type` / `second_type` on
    // std::pair etc.), static data members, and from-base
    // components in addition to padding and code so the
    // operands map to the actual non-static data members.
    // Without this filter, e.g. a brace-init `{x, y}` for
    // `std::pair<T1, T2>` assigns to `first_type` and
    // `second_type` (the public typedefs) and never reaches
    // `first` / `second`, causing the recursive
    // `implicit_typecast(val, struct_tag(typedef))` call to
    // fail with "invalid implicit conversion".
    //
    // Also accept reference-to-class targets: bind the resulting
    // temporary by `address_of`, mirroring the empty-`{}` case.
    if(
      orig_expr.id() == ID_initializer_list && !orig_expr.operands().empty() &&
      (type.id() == ID_struct_tag || type.id() == ID_struct ||
       (type.id() == ID_pointer && is_reference(type))))
    {
      typet base_type = type;
      bool target_is_reference = false;
      if(type.id() == ID_pointer && is_reference(type))
      {
        base_type = to_reference_type(type).base_type();
        target_is_reference = true;
      }
      const bool target_is_struct =
        base_type.id() == ID_struct_tag || base_type.id() == ID_struct;
      const bool target_is_init_list =
        base_type.id() == ID_struct_tag &&
        id2string(to_struct_tag_type(base_type).get_identifier())
            .find("tag-initializer_list<") != std::string::npos;
      if(target_is_struct && !target_is_init_list)
      {
        const struct_typet &st = base_type.id() == ID_struct_tag
                                   ? follow_tag(to_struct_tag_type(base_type))
                                   : to_struct_type(base_type);
        const auto &comps = st.components();
        struct_exprt result({}, base_type);
        std::size_t i = 0;
        bool ok = true;
        for(const auto &c : comps)
        {
          if(
            c.get_is_padding() || c.type().id() == ID_code ||
            c.get_bool(ID_is_type) || c.get_bool(ID_is_static) ||
            c.get_bool(ID_from_base))
            continue;
          if(i < orig_expr.operands().size())
          {
            exprt val = orig_expr.operands()[i++];
            try
            {
              implicit_typecast(val, c.type());
            }
            catch(...)
            {
              ok = false;
              break;
            }
            result.operands().push_back(std::move(val));
          }
          else
          {
            ok = false;
            break;
          }
        }
        if(ok && i == orig_expr.operands().size())
        {
          if(target_is_reference)
          {
            // Materialise a temporary, bind the reference via &temp.
            exprt temp;
            new_temporary(
              orig_expr.source_location(),
              base_type,
              already_typechecked_exprt{std::move(result)},
              temp);
            address_of_exprt addr{temp, pointer_type(base_type)};
            addr.type().set(ID_C_reference, true);
            if(is_rvalue_reference(type))
              addr.type().set(ID_C_rvalue_reference, true);
            expr = std::move(addr);
            return;
          }
          expr = std::move(result);
          return;
        }
      }
    }

    // Brace-init-list to std::initializer_list<T> conversion (C++11):
    // {a, b, c} creates a backing array and constructs the
    // initializer_list with _begin and _size.
    if(
      orig_expr.id() == ID_initializer_list && type.id() == ID_struct_tag &&
      id2string(to_struct_tag_type(type).get_identifier())
          .find("tag-initializer_list<") != std::string::npos)
    {
      const struct_typet &struct_type = follow_tag(to_struct_tag_type(type));
      const auto &components = struct_type.components();

      // Find the element type from the pointer member (_begin or _M_array)
      typet elem_type;
      bool found = false;
      for(const auto &c : components)
      {
        if(
          (c.get_base_name() == "_begin" || c.get_base_name() == "_M_array") &&
          c.type().id() == ID_pointer)
        {
          elem_type = to_pointer_type(c.type()).base_type();
          elem_type.remove(ID_C_constant);
          found = true;
          break;
        }
      }

      if(found)
      {
        const auto &ops = orig_expr.operands();
        const std::size_t n = ops.size();

        // Typecheck each element against T
        exprt::operandst typed_elems;
        bool ok = true;
        for(const auto &op : ops)
        {
          exprt val = op;
          try
          {
            implicit_typecast(val, elem_type);
          }
          catch(...)
          {
            ok = false;
            break;
          }
          typed_elems.push_back(std::move(val));
        }

        if(ok)
        {
          // Create backing array type: T[n]
          const auto arr_type =
            array_typet(elem_type, from_integer(n, size_type()));

          // Create a symbol for the backing array
          const auto arr_id =
            "__init_list_arr$" + std::to_string(anon_counter++);
          auxiliary_symbolt arr_sym;
          arr_sym.name = arr_id;
          arr_sym.base_name = arr_id;
          arr_sym.type = arr_type;
          arr_sym.type.set(ID_C_constant, true);
          arr_sym.mode = ID_cpp;
          arr_sym.is_static_lifetime = true;
          arr_sym.is_lvalue = true;
          arr_sym.location = orig_expr.source_location();
          arr_sym.value = array_exprt(std::move(typed_elems), arr_type);
          symbol_table.add(arr_sym);

          symbol_exprt arr_ref(arr_id, arr_type);
          arr_ref.add_source_location() = orig_expr.source_location();
          // The backing array symbol is created with
          // `is_lvalue = true`; carry that through the symbol_exprt
          // so callers (in particular the `address_of_exprt &arr[0]`
          // built below) see a proper lvalue and downstream uses
          // such as recursive `implicit_typecast` from the brace-
          // init-to-class-with-init_list-ctor handler don't trip
          // the "address_of: not an lvalue" path.
          arr_ref.set(ID_C_lvalue, true);

          // Build struct { &arr[0], n }
          // Find the two data members (pointer and size)
          const struct_typet::componentt *ptr_comp = nullptr;
          const struct_typet::componentt *size_comp = nullptr;
          for(const auto &c : components)
          {
            if(
              c.type().id() == ID_code || c.get_bool(ID_is_type) ||
              c.get_bool(ID_is_static))
            {
              continue;
            }
            if(!ptr_comp)
              ptr_comp = &c;
            else if(!size_comp)
              size_comp = &c;
          }

          if(ptr_comp && size_comp)
          {
            struct_exprt result({}, type);
            index_exprt first_elem(
              arr_ref, from_integer(0, c_index_type()), elem_type);
            address_of_exprt addr(first_elem);
            addr.type() = ptr_comp->type();
            result.add_to_operands(std::move(addr));
            result.add_to_operands(from_integer(n, size_comp->type()));
            result.add_source_location() = orig_expr.source_location();
            expr = std::move(result);
            return;
          }
        }
      }
    }

    // Aggregate initialization from braced-init-list (C++11):
    // { args... } can initialize a POD struct by assigning each element
    // to the corresponding data member.
    if(
      orig_expr.id() == ID_initializer_list && cpp_is_pod(type) &&
      type.id() == ID_struct_tag)
    {
      const struct_typet &struct_type = follow_tag(to_struct_tag_type(type));
      const auto &ops = orig_expr.operands();
      struct_exprt result({}, type);
      std::size_t idx = 0;
      bool ok = true;
      for(const auto &c : struct_type.components())
      {
        if(
          c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
          c.get_bool(ID_is_static) || c.type().id() == ID_code)
        {
          continue;
        }
        if(idx < ops.size())
        {
          exprt val = ops[idx++];
          try
          {
            implicit_typecast(val, c.type());
          }
          catch(...)
          {
            ok = false;
            break;
          }
          result.add_to_operands(std::move(val));
        }
        else
        {
          result.add_to_operands(constant_exprt(irep_idt(), c.type()));
        }
      }
      if(ok)
      {
        expr = std::move(result);
        return;
      }
    }

    // Downgrade to non-fatal when the target type is malformed (e.g.,
    // from failed template instantiation in system headers).  A valid
    // type has a recognized id like signedbv, unsignedbv, struct_tag, etc.
    // An empty or unrecognized id indicates a broken type from template
    // instantiation failure.
    if(id2string(type.id()).empty() || type.is_nil())
    {
      warning().source_location = e.find_source_location();
      warning() << "invalid implicit conversion from '" << to_string(e.type())
                << "' to '" << to_string(type) << "'" << eom;
      e = typecast_exprt(e, type);
      return;
    }

    show_instantiation_stack(error());
    error().source_location = e.find_source_location();
    error() << "invalid implicit conversion from '" << to_string(e.type())
            << "' to '" << to_string(type) << "'" << eom;
    throw 0;
  }
}

/// A reference to type "cv1 T1" is initialized by an expression of
/// type "cv2 T2" as follows:
///
/// - If the initializer expression
///   - is an lvalue (but is not a bit-field), and "cv1 T1" is
///     reference-compatible with "cv2 T2," or
///   - has a class type (i.e., T2 is a class type) and can be
///     implicitly converted to an lvalue of type "cv3 T3," where
///     "cv1 T1" is reference-compatible with "cv3 T3" 92) (this
///     conversion is selected by enumerating the applicable conversion
///     functions (13.3.1.6) and choosing the best one through overload
///     resolution (13.3)),
///
///   then the reference is bound directly to the initializer
///   expression lvalue in the first case, and the reference is
///   bound to the lvalue result of the conversion in the second
///   case. In these cases the reference is said to bind directly
///   to the initializer expression.
///
/// - Otherwise, the reference shall be to a non-volatile const type
///   - If the initializer expression is an rvalue, with T2 a class
///     type, and "cv1 T1" is reference-compatible with "cv2 T2," the
///     reference is bound in one of the following ways (the choice is
///     implementation-defined):
///
///     - The reference is bound to the object represented by the
///       rvalue (see 3.10) or to a sub-object within that object.
///
///     - A temporary of type "cv1 T2" [sic] is created, and a
///       constructor is called to copy the entire rvalue object into
///       the temporary. The reference is bound to the temporary or
///       to a sub-object within the temporary.
///
///     The constructor that would be used to make the copy shall be
///     callable whether or not the copy is actually done.
///
///     Otherwise, a temporary of type "cv1 T1" is created and
///     initialized from the initializer expression using the rules for
///     a non-reference copy initialization (8.5). The reference is then
///     bound to the temporary. If T1 is reference-related to T2, cv1
///     must be the same cv-qualification as, or greater cvqualification
///     than, cv2; otherwise, the program is ill-formed.
void cpp_typecheckt::reference_initializer(
  exprt &expr,
  const reference_typet &reference_type)
{
  add_implicit_dereference(expr);

  unsigned rank = 0;
  exprt new_expr;
  if(reference_binding(expr, reference_type, new_expr, rank))
  {
    expr.swap(new_expr);
    return;
  }

  error().source_location = expr.find_source_location();
  error() << "bad reference initializer" << eom;
  throw 0;
}

bool cpp_typecheckt::cast_away_constness(const typet &t1, const typet &t2) const
{
  PRECONDITION(t1.id() == ID_pointer && t2.id() == ID_pointer);

  // When casting to void* or const void*, only the top-level const
  // qualifier of the source pointer's base type matters.  The generic
  // subtype-chain comparison below breaks when the chains have
  // different depths (e.g., pointer-to-array vs pointer-to-void).
  if(to_pointer_type(t2).base_type().id() == ID_empty)
  {
    c_qualifierst q_from;
    q_from.read(to_pointer_type(t1).base_type());
    c_qualifierst q_to;
    q_to.read(to_pointer_type(t2).base_type());
    return q_from.is_constant && !q_to.is_constant;
  }

  typet nt1 = t1;
  typet nt2 = t2;

  if(is_reference(nt1))
    nt1.remove(ID_C_reference);
  nt1.remove(ID_to_member);

  if(is_reference(nt2))
    nt2.remove(ID_C_reference);
  nt2.remove(ID_to_member);

  // substitute final subtypes
  std::vector<typet> snt1;
  snt1.push_back(nt1);

  while(snt1.back().has_subtype())
  {
    snt1.reserve(snt1.size() + 1);
    snt1.push_back(to_type_with_subtype(snt1.back()).subtype());
  }

  c_qualifierst q1;
  q1.read(snt1.back());

  bool_typet newnt1;
  q1.write(newnt1);
  snt1.back() = newnt1;

  std::vector<typet> snt2;
  snt2.push_back(nt2);
  while(snt2.back().has_subtype())
  {
    snt2.reserve(snt2.size() + 1);
    snt2.push_back(to_type_with_subtype(snt2.back()).subtype());
  }

  c_qualifierst q2;
  q2.read(snt2.back());

  bool_typet newnt2;
  q2.write(newnt2);
  snt2.back() = newnt2;

  const std::size_t k = snt1.size() < snt2.size() ? snt1.size() : snt2.size();

  for(std::size_t i = k; i > 1; i--)
  {
    to_type_with_subtype(snt1[snt1.size() - 2]).subtype() =
      snt1[snt1.size() - 1];
    snt1.pop_back();

    to_type_with_subtype(snt2[snt2.size() - 2]).subtype() =
      snt2[snt2.size() - 1];
    snt2.pop_back();
  }

  exprt e1("Dummy", snt1.back());
  exprt e2;

  return !standard_conversion_qualification(e1, snt2.back(), e2);
}

bool cpp_typecheckt::const_typecast(
  const exprt &expr,
  const typet &type,
  exprt &new_expr)
{
  PRECONDITION(!is_reference(expr.type()));

  exprt curr_expr = expr;

  if(curr_expr.type().id() == ID_array)
  {
    if(type.id() == ID_pointer)
    {
      if(!standard_conversion_array_to_pointer(curr_expr, new_expr))
        return false;
    }
  }
  else if(curr_expr.type().id() == ID_code && type.id() == ID_pointer)
  {
    if(!standard_conversion_function_to_pointer(curr_expr, new_expr))
      return false;
  }
  else if(curr_expr.get_bool(ID_C_lvalue))
  {
    if(!standard_conversion_lvalue_to_rvalue(curr_expr, new_expr))
      return false;
  }
  else
    new_expr = curr_expr;

  if(is_reference(type))
  {
    if(!expr.get_bool(ID_C_lvalue))
      return false;

    typet expr_type_nq = new_expr.type();
    expr_type_nq.remove(ID_C_constant);
    expr_type_nq.remove(ID_C_volatile);
    typet target_type_nq = to_reference_type(type).base_type();
    target_type_nq.remove(ID_C_constant);
    target_type_nq.remove(ID_C_volatile);

    if(expr_type_nq != target_type_nq)
      return false;

    address_of_exprt address_of(expr, to_pointer_type(type));
    add_implicit_dereference(address_of);
    new_expr = address_of;
    return true;
  }
  else if(type.id() == ID_pointer)
  {
    if(type != new_expr.type())
      return false;

    // add proper typecast
    typecast_exprt typecast_expr(expr, type);
    new_expr.swap(typecast_expr);
    return true;
  }

  return false;
}

bool cpp_typecheckt::dynamic_typecast(
  const exprt &expr,
  const typet &type,
  exprt &new_expr)
{
  exprt e(expr);

  if(type.id() == ID_pointer)
  {
    if(e.id() == ID_dereference && e.get_bool(ID_C_implicit))
      e = to_dereference_expr(expr).pointer();

    if(e.type().id() == ID_pointer && cast_away_constness(e.type(), type))
      return false;
  }

  add_implicit_dereference(e);

  if(is_reference(type))
  {
    if(to_reference_type(type).base_type().id() != ID_struct_tag)
      return false;
  }
  else if(type.id() == ID_pointer)
  {
    if(type.find(ID_to_member).is_not_nil())
      return false;

    if(to_pointer_type(type).base_type().id() == ID_empty)
    {
      if(!e.get_bool(ID_C_lvalue))
        return false;
      UNREACHABLE; // currently not supported
    }
    else if(to_pointer_type(type).base_type().id() == ID_struct_tag)
    {
      if(e.get_bool(ID_C_lvalue))
      {
        exprt tmp(e);

        if(!standard_conversion_lvalue_to_rvalue(tmp, e))
          return false;
      }
    }
    else
      return false;
  }
  else
    return false;

  return static_typecast(e, type, new_expr);
}

bool cpp_typecheckt::reinterpret_typecast(
  const exprt &expr,
  const typet &type,
  exprt &new_expr,
  bool check_constantness)
{
  exprt e = expr;

  if(check_constantness && type.id() == ID_pointer)
  {
    if(e.id() == ID_dereference && e.get_bool(ID_C_implicit))
      e = to_dereference_expr(expr).pointer();

    if(e.type().id() == ID_pointer && cast_away_constness(e.type(), type))
      return false;
  }

  add_implicit_dereference(e);

  if(!is_reference(type))
  {
    exprt tmp;

    if(e.id() == ID_code)
    {
      if(standard_conversion_function_to_pointer(e, tmp))
        e.swap(tmp);
      else
        return false;
    }

    if(e.type().id() == ID_array)
    {
      if(standard_conversion_array_to_pointer(e, tmp))
        e.swap(tmp);
      else
        return false;
    }

    if(e.get_bool(ID_C_lvalue))
    {
      if(standard_conversion_lvalue_to_rvalue(e, tmp))
        e.swap(tmp);
      else
        return false;
    }
  }

  if(
    e.type().id() == ID_pointer &&
    (type.id() == ID_unsignedbv || type.id() == ID_signedbv))
  {
    // pointer to integer, always ok
    new_expr = typecast_exprt::conditional_cast(e, type);
    return true;
  }

  if(
    (e.type().id() == ID_unsignedbv || e.type().id() == ID_signedbv ||
     e.type().id() == ID_c_bool || e.is_boolean()) &&
    type.id() == ID_pointer && !is_reference(type))
  {
    // integer to pointer
    if(simplify_expr(e, *this) == 0)
    {
      // NULL
      new_expr = e;
      new_expr.set(ID_value, ID_NULL);
      new_expr.type() = type;
    }
    else
    {
      new_expr = typecast_exprt::conditional_cast(e, type);
    }
    return true;
  }

  if(
    e.type().id() == ID_pointer && type.id() == ID_pointer &&
    !is_reference(type))
  {
    // pointer to pointer: we ok it all.
    // This is more generous than the standard.
    new_expr = typecast_exprt::conditional_cast(expr, type);
    return true;
  }

  if(is_reference(type) && e.get_bool(ID_C_lvalue))
  {
    // Per [expr.reinterpret.cast]/11: a glvalue of type T1 can be cast
    // to a reference-to-T2 if an expression of type "pointer to T1" can
    // be explicitly converted to "pointer to T2" via reinterpret_cast.
    // The resulting glvalue refers to the same storage.
    //
    // In CBMC's IR, `T&` is modelled as `T*` with `C_reference` set.
    // Take the address of the source lvalue, cast it to the target
    // pointer type, and hand it back as the reference value.
    address_of_exprt addr{e};
    typecast_exprt cast_ptr{
      addr, pointer_type(to_reference_type(type).base_type())};
    cast_ptr.type() = type;
    new_expr.swap(cast_ptr);
    return true;
  }

  // reinterpret_cast to reference from an array type (arrays are always
  // lvalues, even when constexpr has replaced the symbol with a constant)
  if(is_reference(type) && e.type().id() == ID_array)
  {
    new_expr = typecast_exprt::conditional_cast(address_of_exprt(e), type);
    return true;
  }

  return false;
}

bool cpp_typecheckt::static_typecast(
  const exprt &expr, // source expression
  const typet &type, // destination type
  exprt &new_expr,
  bool check_constantness)
{
  exprt e = expr;

  if(check_constantness && type.id() == ID_pointer)
  {
    if(e.id() == ID_dereference && e.get_bool(ID_C_implicit))
      e = to_dereference_expr(expr).pointer();

    if(e.type().id() == ID_pointer && cast_away_constness(e.type(), type))
      return false;
  }

  add_implicit_dereference(e);

  // rvalue reference: static_cast<T&&>(expr)
  // Must be checked before lvalue reference since rvalue references
  // also have C_reference set.
  if(type.get_bool(ID_C_rvalue_reference))
  {
    typet subto = to_pointer_type(type).base_type();
    if(e.type() == subto)
    {
      new_expr = address_of_exprt(e, to_pointer_type(type));
      new_expr.add_source_location() = e.source_location();
      return true;
    }
    return false;
  }

  if(type.get_bool(ID_C_reference))
  {
    const reference_typet &reference_type = to_reference_type(type);
    unsigned rank = 0;
    if(reference_binding(e, reference_type, new_expr, rank))
      return true;

    typet subto = reference_type.base_type();
    typet from = e.type();

    if(subto.id() == ID_struct_tag && from.id() == ID_struct_tag)
    {
      if(!expr.get_bool(ID_C_lvalue))
        return false;

      c_qualifierst qual_from;
      qual_from.read(e.type());

      c_qualifierst qual_to;
      qual_to.read(subto);

      if(!qual_to.is_subset_of(qual_from))
        return false;

      const struct_typet &from_struct = follow_tag(to_struct_tag_type(from));
      const struct_typet &subto_struct = follow_tag(to_struct_tag_type(subto));

      if(subtype_typecast(subto_struct, from_struct))
      {
        if(e.id() == ID_dereference)
        {
          make_ptr_typecast(to_dereference_expr(e).pointer(), reference_type);
          new_expr.swap(to_dereference_expr(e).pointer());
          return true;
        }

        exprt address_of = address_of_exprt(e);
        make_ptr_typecast(address_of, reference_type);
        new_expr.swap(address_of);
        return true;
      }
    }
    return false;
  }

  if(type.id() == ID_empty)
  {
    new_expr = typecast_exprt::conditional_cast(e, type);
    return true;
  }

  // int/enum to enum
  if(
    type.id() == ID_c_enum_tag &&
    (e.type().id() == ID_signedbv || e.type().id() == ID_unsignedbv ||
     e.type().id() == ID_c_enum_tag))
  {
    new_expr = typecast_exprt::conditional_cast(e, type);
    new_expr.remove(ID_C_lvalue);
    return true;
  }

  if(implicit_conversion_sequence(e, type, new_expr))
  {
    if(!cpp_is_pod(type))
    {
      exprt temporary;
      new_temporary(
        e.source_location(),
        type,
        already_typechecked_exprt{new_expr},
        temporary);
      new_expr.swap(temporary);
    }
    else
    {
      // try to avoid temporary
      new_expr.set(ID_C_temporary_avoided, true);
      if(new_expr.get_bool(ID_C_lvalue))
        new_expr.remove(ID_C_lvalue);
    }

    return true;
  }

  if(type.id() == ID_pointer && e.type().id() == ID_pointer)
  {
    const pointer_typet &pointer_type = to_pointer_type(type);
    if(type.find(ID_to_member).is_nil() && e.type().find(ID_to_member).is_nil())
    {
      typet to = pointer_type.base_type();
      typet from = to_pointer_type(e.type()).base_type();

      if(from.id() == ID_empty)
      {
        new_expr = typecast_exprt::conditional_cast(e, type);
        return true;
      }

      if(to.id() == ID_empty)
      {
        new_expr = typecast_exprt::conditional_cast(e, type);
        return true;
      }

      if(to.id() == ID_struct_tag && from.id() == ID_struct_tag)
      {
        if(e.get_bool(ID_C_lvalue))
        {
          exprt tmp(e);
          if(!standard_conversion_lvalue_to_rvalue(tmp, e))
            return false;
        }

        const struct_typet &from_struct = follow_tag(to_struct_tag_type(from));
        const struct_typet &to_struct = follow_tag(to_struct_tag_type(to));
        if(subtype_typecast(to_struct, from_struct))
        {
          make_ptr_typecast(e, pointer_type);
          new_expr.swap(e);
          return true;
        }
      }

      return false;
    }
    else if(
      type.find(ID_to_member).is_not_nil() &&
      e.type().find(ID_to_member).is_not_nil())
    {
      if(pointer_type.base_type() != to_pointer_type(e.type()).base_type())
        return false;

      const struct_typet &from_struct = follow_tag(to_struct_tag_type(
        static_cast<const typet &>(e.type().find(ID_to_member))));

      const struct_typet &to_struct = follow_tag(to_struct_tag_type(
        static_cast<const typet &>(type.find(ID_to_member))));

      if(subtype_typecast(from_struct, to_struct))
      {
        new_expr = typecast_exprt::conditional_cast(e, type);
        return true;
      }
    }
    else if(
      type.find(ID_to_member).is_nil() &&
      e.type().find(ID_to_member).is_not_nil())
    {
      if(pointer_type.base_type() != to_pointer_type(e.type()).base_type())
      {
        return false;
      }

      const struct_tag_typet &from_struct_tag = to_struct_tag_type(
        static_cast<const typet &>(e.type().find(ID_to_member)));

      new_expr = e;
      new_expr.type().add(ID_to_member) = from_struct_tag;

      return true;
    }
    else
      return false;
  }

  return false;
}
