/*******************************************************************\

Module: C++ Language Type Checking

Author:

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#include <cstdlib>

#include <util/arith_tools.h>
#include <util/config.h>
#include <util/expr_util.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <ansi-c/c_qualifiers.h>
#include <util/c_types.h>

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
  assert(expr.get_bool(ID_C_lvalue));

  if(expr.type().id() == ID_code)
    return false;

  if(
    expr.type().id() == ID_struct &&
    to_struct_type(expr.type()).is_incomplete())
    return false;

  if(expr.type().id() == ID_union && to_union_type(expr.type()).is_incomplete())
    return false;

  new_expr=expr;
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
  assert(expr.type().id()==ID_array);

  index_exprt index(
    expr,
    from_integer(0, index_type()));

  index.set(ID_C_lvalue, true);

  new_expr=address_of_exprt(index);

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
  const exprt &expr, exprt &new_expr) const
{
  if(!expr.get_bool(ID_C_lvalue))
    return false;

  new_expr=address_of_exprt(expr);

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
  if(expr.type().id()!=ID_pointer ||
     is_reference(expr.type()))
    return false;

  if(expr.get_bool(ID_C_lvalue))
    return false;

  if(expr.type()!=type)
    return false;

  typet sub_from=expr.type().subtype();
  typet sub_to=type.subtype();
  bool const_to=true;

  while(sub_from.id()==ID_pointer)
  {
    c_qualifierst qual_from(sub_from);
    c_qualifierst qual_to(sub_to);

    if(!qual_to.is_constant)
      const_to=false;

    if(qual_from.is_constant && !qual_to.is_constant)
      return false;

    if(qual_from!=qual_to && !const_to)
      return false;

    typet tmp1=sub_from.subtype();
    sub_from.swap(tmp1);

    typet tmp2=sub_to.subtype();
    sub_to.swap(tmp2);
  }

  c_qualifierst qual_from(sub_from);
  c_qualifierst qual_to(sub_to);

  if(qual_from.is_subset_of(qual_to))
  {
    new_expr=expr;
    new_expr.type()=type;
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

  typet int_type=signed_int_type();
  qual_from.write(int_type);

  if(expr.type().id()==ID_signedbv)
  {
    std::size_t width=to_signedbv_type(expr.type()).get_width();
    if(width >= config.ansi_c.int_width)
      return false;
    new_expr=expr;
    new_expr.make_typecast(int_type);
    return true;
  }

  if(expr.type().id()==ID_unsignedbv)
  {
    std::size_t width=to_unsignedbv_type(expr.type()).get_width();
    if(width >= config.ansi_c.int_width)
      return false;
    new_expr=expr;
    if(width==config.ansi_c.int_width)
      int_type.id(ID_unsignedbv);
    new_expr.make_typecast(int_type);
    return true;
  }

  if(expr.type().id() == ID_bool || expr.type().id() == ID_c_bool)
  {
    new_expr = expr;
    new_expr.make_typecast(int_type);
    return true;
  }

  if(expr.type().id()==ID_c_enum_tag)
  {
    new_expr=expr;
    new_expr.make_typecast(int_type);
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
  if(expr.type()!=float_type())
    return false;

  std::size_t width=to_floatbv_type(expr.type()).get_width();

  if(width!=config.ansi_c.single_width)
    return false;

  c_qualifierst qual_from;
  qual_from.read(expr.type());

  new_expr=expr;
  new_expr.make_typecast(double_type());
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
  if(type.id()!=ID_signedbv &&
     type.id()!=ID_unsignedbv)
      return false;

  if(
    expr.type().id() != ID_signedbv && expr.type().id() != ID_unsignedbv &&
    expr.type().id() != ID_c_bool && expr.type().id() != ID_bool &&
    expr.type().id() != ID_c_enum_tag)
  {
    return false;
  }

  if(expr.get_bool(ID_C_lvalue))
    return false;

  c_qualifierst qual_from;
  qual_from.read(expr.type());
  new_expr=expr;
  new_expr.make_typecast(type);
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

  if(expr.type().id()==ID_floatbv ||
     expr.type().id()==ID_fixedbv)
  {
    if(type.id()!=ID_signedbv &&
       type.id()!=ID_unsignedbv)
      return false;
  }
  else if(expr.type().id()==ID_signedbv ||
          expr.type().id()==ID_unsignedbv ||
          expr.type().id()==ID_c_enum_tag)
  {
    if(type.id()!=ID_fixedbv &&
       type.id()!=ID_floatbv)
      return false;
  }
  else
    return false;

  c_qualifierst qual_from;
  qual_from.read(expr.type());
  new_expr=expr;
  new_expr.make_typecast(type);
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
  if(expr.type().id()!=ID_floatbv &&
     expr.type().id()!=ID_fixedbv)
    return false;

  if(type.id()!=ID_floatbv &&
     type.id()!=ID_fixedbv)
      return false;

  if(expr.get_bool(ID_C_lvalue))
    return false;

  c_qualifierst qual_from;

  qual_from.read(expr.type());
  new_expr=expr;
  new_expr.make_typecast(type);
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
  if(type.id()!=ID_pointer ||
     is_reference(type))
    return false;

  if(expr.get_bool(ID_C_lvalue))
    return false;

  // integer 0 to NULL pointer conversion?
  if(simplify_expr(expr, *this).is_zero() &&
     expr.type().id()!=ID_pointer)
  {
    new_expr=expr;
    new_expr.set(ID_value, ID_NULL);
    new_expr.type()=type;
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

  typet sub_from=follow(expr.type().subtype());
  typet sub_to=follow(type.subtype());

  // std::nullptr_t to _any_ pointer type
  if(sub_from.id()==ID_nullptr)
    return true;

  // anything but function pointer to void *
  if(sub_from.id()!=ID_code && sub_to.id()==ID_empty)
  {
    c_qualifierst qual_from;
    qual_from.read(expr.type().subtype());
    new_expr=expr;
    new_expr.make_typecast(type);
    qual_from.write(new_expr.type().subtype());
    return true;
  }

  // struct * to struct *
  if(sub_from.id()==ID_struct && sub_to.id()==ID_struct)
  {
    const struct_typet &from_struct=to_struct_type(sub_from);
    const struct_typet &to_struct=to_struct_type(sub_to);
    if(subtype_typecast(from_struct, to_struct))
    {
      c_qualifierst qual_from;
      qual_from.read(expr.type().subtype());
      new_expr=expr;
      make_ptr_typecast(new_expr, type);
      qual_from.write(new_expr.type().subtype());
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

  if(type.subtype()!=expr.type().subtype())
  {
    // subtypes different
    if(type.subtype().id()==ID_code  &&
       expr.type().subtype().id()==ID_code)
    {
      code_typet code1=to_code_type(expr.type().subtype());
      assert(!code1.parameters().empty());
      code_typet::parametert this1=code1.parameters()[0];
      assert(this1.get(ID_C_base_name)==ID_this);
      code1.parameters().erase(code1.parameters().begin());

      code_typet code2=to_code_type(type.subtype());
      assert(!code2.parameters().empty());
      code_typet::parametert this2=code2.parameters()[0];
      assert(this2.get(ID_C_base_name)==ID_this);
      code2.parameters().erase(code2.parameters().begin());

      if(this2.type().subtype().get_bool(ID_C_constant) &&
         !this1.type().subtype().get_bool(ID_C_constant))
        return false;

      // give a second chance ignoring `this'
      if(code1!=code2)
        return false;
    }
    else
      return false;
  }

  if(expr.get_bool(ID_C_lvalue))
    return false;

  if(expr.id()==ID_constant &&
     expr.get(ID_value)==ID_NULL)
  {
    new_expr=expr;
    new_expr.make_typecast(type);
    return true;
  }

  struct_typet from_struct = to_struct_type(
    follow(static_cast<const typet &>(expr.type().find(ID_to_member))));

  struct_typet to_struct =
    to_struct_type(follow(static_cast<const typet &>(type.find(ID_to_member))));

  if(subtype_typecast(to_struct, from_struct))
  {
    new_expr=expr;
    new_expr.make_typecast(type);
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
  const exprt &expr, exprt &new_expr) const
{
  if(expr.get_bool(ID_C_lvalue))
    return false;

  if(
    expr.type().id() != ID_signedbv && expr.type().id() != ID_unsignedbv &&
    expr.type().id() != ID_pointer && expr.type().id() != ID_bool &&
    expr.type().id() != ID_c_enum_tag)
  {
    return false;
  }

  c_qualifierst qual_from;
  qual_from.read(expr.type());

  typet Bool = c_bool_type();
  qual_from.write(Bool);

  new_expr=expr;
  new_expr.make_typecast(Bool);
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
  assert(!is_reference(expr.type()) && !is_reference(type));

  exprt curr_expr=expr;

  // bit fields are converted like their underlying type
  if(type.id()==ID_c_bit_field)
    return standard_conversion_sequence(expr, type.subtype(), new_expr, rank);

  // we turn bit fields into their underlying type
  if(curr_expr.type().id()==ID_c_bit_field)
    curr_expr.make_typecast(curr_expr.type().subtype());

  if(curr_expr.type().id()==ID_array)
  {
    if(type.id()==ID_pointer)
    {
      if(!standard_conversion_array_to_pointer(curr_expr, new_expr))
        return false;
    }
  }
  else if(curr_expr.type().id()==ID_code &&
          type.id()==ID_pointer)
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
    new_expr=curr_expr;

  curr_expr.swap(new_expr);

  // two enums are the same if the tag is the same,
  // even if the width differs (enum bit-fields!)
  if(follow(type).id()==ID_c_enum &&
     follow(curr_expr.type()).id()==ID_c_enum)
  {
    if(follow(type).find(ID_tag)==
       follow(curr_expr.type()).find(ID_tag))
      return true;
    else
    {
      // In contrast to C, we simply don't allow implicit conversions
      // between enums.
      return false;
    }
  }

  // need to consider #c_type
  if(follow(curr_expr.type())!=follow(type) ||
     curr_expr.type().get(ID_C_c_type)!=type.get(ID_C_c_type))
  {
    if(type.id()==ID_signedbv ||
       type.id()==ID_unsignedbv ||
       follow(type).id()==ID_c_enum)
    {
      if(!standard_conversion_integral_promotion(curr_expr, new_expr) ||
         new_expr.type() != type)
      {
        if(!standard_conversion_integral_conversion(curr_expr, type, new_expr))
        {
          if(!standard_conversion_floating_integral_conversion(
              curr_expr, type, new_expr))
            return false;
        }

        rank+=3;
      }
      else
        rank+=2;
    }
    else if(type.id()==ID_floatbv || type.id()==ID_fixedbv)
    {
      if(!standard_conversion_floating_point_promotion(curr_expr, new_expr) ||
         new_expr.type() != type)
      {
        if(!standard_conversion_floating_point_conversion(
            curr_expr, type, new_expr) &&
           !standard_conversion_floating_integral_conversion(
             curr_expr, type, new_expr))
          return false;

        rank += 3;
      }
      else
        rank += 2;
    }
    else if(type.id()==ID_pointer)
    {
      if(expr.type().subtype().id()==ID_nullptr)
      {
        // std::nullptr_t to _any_ pointer type is ok
        new_expr.make_typecast(type);
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
      new_expr = is_not_zero(curr_expr, *this);

      rank += 3;
    }
    else
      return false;
  }
  else
    new_expr=curr_expr;

  curr_expr.swap(new_expr);

  if(curr_expr.type().id()==ID_pointer)
  {
    typet sub_from=curr_expr.type();
    typet sub_to=type;

    do
    {
      typet tmp_from=sub_from.subtype();
      sub_from.swap(tmp_from);
      typet tmp_to=sub_to.subtype();
      sub_to.swap(tmp_to);

      c_qualifierst qual_from;
      qual_from.read(sub_from);

      c_qualifierst qual_to;
      qual_to.read(sub_to);

      if(qual_from!=qual_to)
      {
        rank+=1;
        break;
      }
    }
    while(sub_from.id()==ID_pointer);

    if(!standard_conversion_qualification(curr_expr, type, new_expr))
      return false;
  }
  else
  {
    new_expr=curr_expr;
    new_expr.type()=type;
  }

  return true;
}

/// User-defined conversion sequence
/// \par parameters: A typechecked expression 'expr', a destination
/// type 'type'.
/// \return True iff a user-defined conversion sequence exists. The result of
///   the conversion is stored in 'new_expr'.
bool cpp_typecheckt::user_defined_conversion_sequence(
  const exprt &expr,
  const typet &type,
  exprt &new_expr,
  unsigned &rank)
{
  assert(!is_reference(expr.type()));
  assert(!is_reference(type));

  const typet &from=follow(expr.type());
  const typet &to=follow(type);

  new_expr.make_nil();

  // special case:
  // A conversion from a type to the same type is given an exact
  // match rank even though a user-defined conversion is used

  if(from==to)
    rank+=0;
  else
    rank+=4; // higher than all the standard conversions

  if(to.id()==ID_struct)
  {
    std::string err_msg;

    if(cpp_is_pod(to))
    {
      if(from.id()==ID_struct)
      {
        const struct_typet &from_struct=to_struct_type(from);
        const struct_typet &to_struct=to_struct_type(to);

        // potentially requires
        // expr.get_bool(ID_C_lvalue) ??

        if(subtype_typecast(from_struct, to_struct))
        {
          exprt address=address_of_exprt(expr);

          // simplify address
          if(expr.id()==ID_dereference)
            address=expr.op0();

          pointer_typet ptr_sub=pointer_type(type);
          c_qualifierst qual_from;
          qual_from.read(expr.type());
          qual_from.write(ptr_sub.subtype());
          make_ptr_typecast(address, ptr_sub);

          const dereference_exprt deref(address);

          // create temporary object
          side_effect_exprt tmp_object_expr(
            ID_temporary_object, type, expr.source_location());
          tmp_object_expr.copy_to_operands(deref);
          tmp_object_expr.set(ID_C_lvalue, true);

          new_expr.swap(tmp_object_expr);
          return true;
        }
      }
    }
    else
    {
      bool found=false;

      for(const auto &component : to_struct_type(to).components())
      {
        if(component.get_bool(ID_from_base))
          continue;

        if(component.get_bool(ID_is_explicit))
          continue;

        const typet &comp_type = component.type();

        if(comp_type.id() !=ID_code)
          continue;

        if(to_code_type(comp_type).return_type().id() != ID_constructor)
          continue;

        // TODO: ellipsis

        const auto &parameters = to_code_type(comp_type).parameters();

        if(parameters.size() != 2)
          continue;

        exprt curr_arg1 = parameters[1];
        typet arg1_type=curr_arg1.type();

        if(is_reference(arg1_type))
        {
          typet tmp=arg1_type.subtype();
          arg1_type.swap(tmp);
        }

        unsigned tmp_rank=0;
        if(arg1_type.id() != ID_struct_tag)
        {
            exprt tmp_expr;
            if(standard_conversion_sequence(
                expr, arg1_type, tmp_expr, tmp_rank))
            {
              // check if it's ambiguous
              if(found)
                return false;
              found=true;

              if(expr.get_bool(ID_C_lvalue))
                tmp_expr.set(ID_C_lvalue, true);

              tmp_expr.add_source_location()=expr.source_location();

              exprt func_symb = cpp_symbol_expr(lookup(component.get_name()));
              func_symb.type()=comp_type;
              {
                exprt tmp(ID_already_typechecked);
                tmp.copy_to_operands(func_symb);
                func_symb.swap(func_symb);
              }

              // create temporary object
              side_effect_expr_function_callt ctor_expr;
              ctor_expr.add_source_location()=expr.source_location();
              ctor_expr.function().swap(func_symb);
              ctor_expr.arguments().push_back(tmp_expr);
              typecheck_side_effect_function_call(ctor_expr);

              new_expr.swap(ctor_expr);
              assert(new_expr.get(ID_statement)==ID_temporary_object);

              if(to.get_bool(ID_C_constant))
                new_expr.type().set(ID_C_constant, true);

              rank += tmp_rank;
            }
          }
          else if(from.id() == ID_struct && arg1_type.id() == ID_struct_tag)
          {
            // try derived-to-base conversion
            address_of_exprt expr_pfrom(expr, pointer_type(expr.type()));
            pointer_typet pto=pointer_type(arg1_type);

            exprt expr_ptmp;
            tmp_rank=0;
            if(standard_conversion_sequence(
                expr_pfrom, pto, expr_ptmp, tmp_rank))
            {
              // check if it's ambiguous
              if(found)
                return false;
              found=true;

              rank+=tmp_rank;

              // create temporary object
              dereference_exprt expr_deref(expr_ptmp);
              expr_deref.set(ID_C_lvalue, true);
              expr_deref.add_source_location()=expr.source_location();

              exprt new_object(ID_new_object, type);
              new_object.set(ID_C_lvalue, true);
              new_object.type().set(ID_C_constant, false);

              exprt func_symb = cpp_symbol_expr(lookup(component.get_name()));
              func_symb.type()=comp_type;
              {
                exprt tmp(ID_already_typechecked);
                tmp.copy_to_operands(func_symb);
                func_symb.swap(func_symb);
              }

              side_effect_expr_function_callt ctor_expr;
              ctor_expr.add_source_location()=expr.source_location();
              ctor_expr.function().swap(func_symb);
              ctor_expr.arguments().push_back(expr_deref);
              typecheck_side_effect_function_call(ctor_expr);

              new_expr.swap(ctor_expr);

              INVARIANT(
                new_expr.get(ID_statement)==ID_temporary_object,
                "statement ID");

              if(to.get_bool(ID_C_constant))
                new_expr.type().set(ID_C_constant, true);
            }
          }
        }
        if(found)
          return true;
      }
  }

  // conversion operators
  if(from.id()==ID_struct)
  {
    bool found=false;
    for(const auto &component : to_struct_type(from).components())
    {
      if(component.get_bool(ID_from_base))
        continue;

      if(!component.get_bool(ID_is_cast_operator))
        continue;

      const code_typet &comp_type = to_code_type(component.type());
      DATA_INVARIANT(
        comp_type.parameters().size() == 1, "expected exactly one parameter");

      typet this_type = comp_type.parameters().front().type();
      this_type.set(ID_C_reference, true);

      exprt this_expr(expr);
      this_type.set(ID_C_this, true);

      unsigned tmp_rank=0;
      exprt tmp_expr;

      if(implicit_conversion_sequence(
        this_expr, this_type, tmp_expr, tmp_rank))
      {
        // To take care of the possible virtual case,
        // we build the function as a member expression.
        const cpp_namet cpp_func_name(component.get_base_name());

        exprt member_func(ID_member);
        member_func.add(ID_component_cpp_name)=cpp_func_name;
        exprt ac(ID_already_typechecked);
        ac.copy_to_operands(expr);
        member_func.copy_to_operands(ac);

        side_effect_expr_function_callt func_expr;
        func_expr.add_source_location()=expr.source_location();
        func_expr.function().swap(member_func);
        typecheck_side_effect_function_call(func_expr);

        if(standard_conversion_sequence(func_expr, type, tmp_expr, tmp_rank))
        {
          // check if it's ambiguous
          if(found)
            return false;
          found=true;

          rank+=tmp_rank;
          new_expr.swap(tmp_expr);
        }
      }
    }
    if(found)
      return true;
  }

  return new_expr.is_not_nil();
}

/// Reference-related
/// \par parameters: A typechecked expression 'expr',
/// a reference 'type'.
/// \return True iff an the reference 'type' is reference-related to 'expr'.
bool cpp_typecheckt::reference_related(
  const exprt &expr,
  const typet &type) const
{
  assert(is_reference(type));
  assert(!is_reference(expr.type()));

  typet from=follow(expr.type());
  typet to=follow(type.subtype());

  // need to check #c_type
  if(from.get(ID_C_c_type)!=to.get(ID_C_c_type))
    return false;

  if(from==to)
    return true;

  if(from.id()==ID_struct &&
     to.id()==ID_struct)
    return subtype_typecast(to_struct_type(from),
                            to_struct_type(to));

  if(from.id()==ID_struct &&
     type.get_bool(ID_C_this) &&
     type.subtype().id()==ID_empty)
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
  const typet &type,
  unsigned &rank) const
{
  assert(is_reference(type));
  assert(!is_reference(expr.type()));

  if(!reference_related(expr, type))
    return false;

  if(expr.type()!=type.subtype())
    rank+=3;

  c_qualifierst qual_from;
    qual_from.read(expr.type());

  c_qualifierst qual_to;
    qual_to.read(type.subtype());

  if(qual_from!=qual_to)
    rank+=1;

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
  const typet &type,
  exprt &new_expr,
  unsigned &rank)
{
  assert(is_reference(type));
  assert(!is_reference(expr.type()));

  unsigned backup_rank=rank;

  if(type.get_bool(ID_C_this) &&
     !expr.get_bool(ID_C_lvalue))
  {
    // `this' has to be an lvalue
    if(expr.get(ID_statement)==ID_temporary_object)
      expr.set(ID_C_lvalue, true);
    else if(expr.get(ID_statement)==ID_function_call)
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

  if(expr.get_bool(ID_C_lvalue))
  {
    if(reference_compatible(expr, type, rank))
    {
      {
        address_of_exprt tmp(expr, reference_type(expr.type()));
        tmp.add_source_location()=expr.source_location();
        new_expr.swap(tmp);
      }

      if(expr.type()!=type.subtype())
      {
        c_qualifierst qual_from;
        qual_from.read(expr.type());
        new_expr.make_typecast(type);
        qual_from.write(new_expr.type().subtype());
      }

      return true;
    }

    rank=backup_rank;
  }

  // conversion operators
  const typet &from_type = follow(expr.type());
  if(from_type.id()==ID_struct)
  {
    for(const auto &component : to_struct_type(from_type).components())
    {
      if(component.get_bool(ID_from_base))
        continue;

      if(!component.get_bool(ID_is_cast_operator))
        continue;

      const code_typet &component_type = to_code_type(component.type());

      // otherwise it cannot bind directly (not an lvalue)
      if(!is_reference(component_type.return_type()))
        continue;

      assert(component_type.parameters().size()==1);

      typet this_type =
        component_type.parameters().front().type();
      this_type.set(ID_C_reference, true);

      exprt this_expr(expr);

      this_type.set(ID_C_this, true);

      unsigned tmp_rank=0;

      exprt tmp_expr;
      if(implicit_conversion_sequence(
        this_expr, this_type, tmp_expr, tmp_rank))
      {
        // To take care of the possible virtual case,
        // we build the function as a member expression.
        const cpp_namet cpp_func_name(component.get_base_name());

        exprt member_func(ID_member);
        member_func.add(ID_component_cpp_name)=cpp_func_name;
        exprt ac(ID_already_typechecked);
        ac.copy_to_operands(expr);
        member_func.copy_to_operands(ac);

        side_effect_expr_function_callt func_expr;
        func_expr.add_source_location()=expr.source_location();
        func_expr.function().swap(member_func);
        typecheck_side_effect_function_call(func_expr);

        // let's check if the returned value binds directly
        exprt returned_value=func_expr;
        add_implicit_dereference(returned_value);

        if(returned_value.get_bool(ID_C_lvalue) &&
           reference_compatible(returned_value, type, rank))
        {
          // returned values are lvalues in case of references only
          assert(returned_value.id()==ID_dereference &&
                 is_reference(returned_value.op0().type()));

          new_expr=returned_value.op0();

          if(returned_value.type() != type.subtype())
          {
            c_qualifierst qual_from;
            qual_from.read(returned_value.type());
            make_ptr_typecast(new_expr, type);
            qual_from.write(new_expr.type().subtype());
          }
          rank+=4+tmp_rank;
          return true;
        }
      }
    }
  }

  // No temporary allowed for `this'
  if(type.get_bool(ID_C_this))
    return false;

  if(!type.subtype().get_bool(ID_C_constant) ||
     type.subtype().get_bool(ID_C_volatile))
    return false;

  // TODO: handle the case for implicit parameters
  if(!type.subtype().get_bool(ID_C_constant) &&
     !expr.get_bool(ID_C_lvalue))
    return false;

  exprt arg_expr=expr;

  if(arg_expr.type().id() == ID_struct_tag)
  {
    // required to initialize the temporary
    arg_expr.set(ID_C_lvalue, true);
  }

  if(user_defined_conversion_sequence(arg_expr, type.subtype(), new_expr, rank))
  {
    address_of_exprt tmp(new_expr, reference_type(new_expr.type()));
    tmp.add_source_location()=new_expr.source_location();
    new_expr.swap(tmp);
    return true;
  }

  rank=backup_rank;
  if(standard_conversion_sequence(expr, type.subtype(), new_expr, rank))
  {
    {
      // create temporary object
      exprt tmp=exprt(ID_side_effect, type.subtype());
      tmp.set(ID_statement, ID_temporary_object);
      tmp.add_source_location()=expr.source_location();
      // tmp.set(ID_C_lvalue, true);
      tmp.add_to_operands(std::move(new_expr));
      new_expr.swap(tmp);
    }

    address_of_exprt tmp(new_expr, pointer_type(new_expr.type()));
    tmp.type().set(ID_C_reference, true);
    tmp.add_source_location()=new_expr.source_location();

    new_expr=tmp;
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
  unsigned backup_rank=rank;

  exprt e=expr;
  add_implicit_dereference(e);

  if(is_reference(type))
  {
    if(!reference_binding(e, type, new_expr, rank))
      return false;

    #if 0
    simplify_exprt simplify(*this);
    simplify.simplify(new_expr);
    new_expr.type().set(ID_C_reference, true);
    #endif
  }
  else if(!standard_conversion_sequence(e, type, new_expr, rank))
  {
    rank=backup_rank;
    if(!user_defined_conversion_sequence(e, type, new_expr, rank))
      return false;

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
  unsigned rank=0;
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
  exprt e=expr;

  if(
    e.id() == ID_initializer_list && cpp_is_pod(type) &&
    e.operands().size() == 1)
  {
    e = expr.op0();
  }

  if(!implicit_conversion_sequence(e, type, expr))
  {
    show_instantiation_stack(error());
    error().source_location=e.find_source_location();
    error() << "invalid implicit conversion from `"
            << to_string(e.type()) << "' to `"
            << to_string(type) << "'" << eom;
    #if 0
    str << "\n " << follow(e.type()).pretty() << '\n';
    str << "\n " << type.pretty() << '\n';
    #endif
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
  const typet &type)
{
  assert(is_reference(type));
  add_implicit_dereference(expr);

  unsigned rank=0;
  exprt new_expr;
  if(reference_binding(expr, type, new_expr, rank))
  {
    expr.swap(new_expr);
    return;
  }

  error().source_location=expr.find_source_location();
  error() << "bad reference initializer" << eom;
  throw 0;
}

bool cpp_typecheckt::cast_away_constness(
  const typet &t1,
  const typet &t2) const
{
  assert(t1.id()==ID_pointer && t2.id()==ID_pointer);
  typet nt1=t1;
  typet nt2=t2;

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
    snt1.reserve(snt1.size()+1);
    snt1.push_back(snt1.back().subtype());
  }

  c_qualifierst q1;
  q1.read(snt1.back());

  bool_typet newnt1;
  q1.write(newnt1);
  snt1.back()=newnt1;

  std::vector<typet> snt2;
  snt2.push_back(nt2);
  while(snt2.back().has_subtype())
  {
    snt2.reserve(snt2.size()+1);
    snt2.push_back(snt2.back().subtype());
  }

  c_qualifierst q2;
  q2.read(snt2.back());

  bool_typet newnt2;
  q2.write(newnt2);
  snt2.back()=newnt2;

  const std::size_t k=snt1.size() < snt2.size() ? snt1.size() : snt2.size();

  for(std::size_t i=k; i > 1; i--)
  {
    snt1[snt1.size()-2].subtype()=snt1[snt1.size()-1];
    snt1.pop_back();

    snt2[snt2.size()-2].subtype()=snt2[snt2.size()-1];
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

  exprt curr_expr=expr;

  if(curr_expr.type().id()==ID_array)
  {
    if(type.id()==ID_pointer)
    {
      if(!standard_conversion_array_to_pointer(curr_expr, new_expr))
        return false;
    }
  }
  else if(curr_expr.type().id()==ID_code &&
          type.id()==ID_pointer)
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
    new_expr=curr_expr;

  if(is_reference(type))
  {
    if(!expr.get_bool(ID_C_lvalue))
      return false;

    if(new_expr.type()!=type.subtype())
      return false;

    address_of_exprt address_of(expr, to_pointer_type(type));
    add_implicit_dereference(address_of);
    new_expr=address_of;
    return true;
  }
  else if(type.id()==ID_pointer)
  {
    if(type!=new_expr.type())
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

  if(type.id()==ID_pointer)
  {
    if(e.id()==ID_dereference && e.get_bool(ID_C_implicit))
      e=expr.op0();

    if(e.type().id()==ID_pointer &&
       cast_away_constness(e.type(), type))
      return false;
  }

  add_implicit_dereference(e);

  if(is_reference(type))
  {
    if(type.subtype().id() != ID_struct_tag)
      return false;
  }
  else if(type.id()==ID_pointer)
  {
    if(type.find(ID_to_member).is_not_nil())
      return false;

    if(type.subtype().id()==ID_empty)
    {
      if(!e.get_bool(ID_C_lvalue))
        return false;
      UNREACHABLE; // currently not supported
    }
    else if(type.subtype().id() == ID_struct_tag)
    {
      if(e.get_bool(ID_C_lvalue))
      {
        exprt tmp(e);

        if(!standard_conversion_lvalue_to_rvalue(tmp, e))
          return false;
      }
    }
    else return false;
  }
  else return false;

  return static_typecast(e, type, new_expr);
}

bool cpp_typecheckt::reinterpret_typecast(
  const exprt &expr,
  const typet &type,
  exprt &new_expr,
  bool check_constantness)
{
  exprt e=expr;

  if(check_constantness && type.id()==ID_pointer)
  {
    if(e.id()==ID_dereference && e.get_bool(ID_C_implicit))
      e=expr.op0();

    if(e.type().id()==ID_pointer &&
       cast_away_constness(e.type(), type))
      return false;
  }

  add_implicit_dereference(e);

  if(!is_reference(type))
  {
    exprt tmp;

    if(e.id()==ID_code)
    {
      if(standard_conversion_function_to_pointer(e, tmp))
         e.swap(tmp);
      else
        return false;
    }

    if(e.type().id()==ID_array)
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

  if(e.type().id()==ID_pointer &&
     (type.id()==ID_unsignedbv || type.id()==ID_signedbv))
  {
    // pointer to integer, always ok
    new_expr=e;
    new_expr.make_typecast(type);
    return true;
  }

  if(
    (e.type().id() == ID_unsignedbv || e.type().id() == ID_signedbv ||
     e.type().id() == ID_c_bool || e.type().id() == ID_bool) &&
    type.id() == ID_pointer && !is_reference(type))
  {
    // integer to pointer
    if(simplify_expr(e, *this).is_zero())
    {
      // NULL
      new_expr=e;
      new_expr.set(ID_value, ID_NULL);
      new_expr.type()=type;
    }
    else
    {
      new_expr=e;
      new_expr.make_typecast(type);
    }
    return true;
  }

  if(e.type().id()==ID_pointer &&
     type.id()==ID_pointer &&
     !is_reference(type))
  {
    // pointer to pointer: we ok it all.
    // This is more generous than the standard.
    new_expr=expr;
    new_expr.make_typecast(type);
    return true;
  }

  if(is_reference(type) && e.get_bool(ID_C_lvalue))
  {
    exprt tmp=address_of_exprt(e);
    tmp.make_typecast(type);
    new_expr.swap(tmp);
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
  exprt e=expr;

  if(check_constantness && type.id()==ID_pointer)
  {
    if(e.id()==ID_dereference && e.get_bool(ID_C_implicit))
      e=expr.op0();

    if(e.type().id()==ID_pointer &&
       cast_away_constness(e.type(), type))
      return false;
  }

  add_implicit_dereference(e);

  if(type.get_bool(ID_C_reference))
  {
    unsigned rank=0;
    if(reference_binding(e, type, new_expr, rank))
      return true;

    typet subto=follow(type.subtype());
    typet from=follow(e.type());

    if(subto.id()==ID_struct && from.id()==ID_struct)
    {
      if(!expr.get_bool(ID_C_lvalue))
        return false;

      c_qualifierst qual_from;
      qual_from.read(e.type());

      c_qualifierst qual_to;
      qual_to.read(type.subtype());

      if(!qual_to.is_subset_of(qual_from))
        return false;

      struct_typet from_struct=to_struct_type(from);
      struct_typet subto_struct=to_struct_type(subto);

      if(subtype_typecast(subto_struct, from_struct))
      {
        if(e.id()==ID_dereference)
        {
          make_ptr_typecast(e.op0(), type);
          new_expr.swap(e.op0());
          return true;
        }

        exprt address_of=address_of_exprt(e);
        make_ptr_typecast(address_of, type);
        new_expr.swap(address_of);
        return true;
      }
    }
    return false;
  }

  if(type.id()==ID_empty)
  {
    new_expr=e;
    new_expr.make_typecast(type);
    return true;
  }

  // int/enum to enum
  if(type.id()==ID_c_enum_tag &&
     (e.type().id()==ID_signedbv ||
      e.type().id()==ID_unsignedbv ||
      e.type().id()==ID_c_enum_tag))
  {
    new_expr=e;
    new_expr.make_typecast(type);
    new_expr.remove(ID_C_lvalue);
    return true;
  }

  if(implicit_conversion_sequence(e, type, new_expr))
  {
    if(!cpp_is_pod(type))
    {
      exprt tc(ID_already_typechecked);
      tc.copy_to_operands(new_expr);
      exprt temporary;
      new_temporary(e.source_location(), type, tc, temporary);
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

  if(type.id()==ID_pointer && e.type().id()==ID_pointer)
  {
    if(type.find(ID_to_member).is_nil() && e.type().find(ID_to_member).is_nil())
    {
      typet to=follow(type.subtype());
      typet from=follow(e.type().subtype());

      if(from.id()==ID_empty)
      {
          e.make_typecast(type);
          new_expr.swap(e);
          return true;
      }

      if(to.id()==ID_struct && from.id()==ID_struct)
      {
        if(e.get_bool(ID_C_lvalue))
        {
          exprt tmp(e);
          if(!standard_conversion_lvalue_to_rvalue(tmp, e))
            return false;
        }

        struct_typet from_struct=to_struct_type(from);
        struct_typet to_struct=to_struct_type(to);
        if(subtype_typecast(to_struct, from_struct))
        {
          make_ptr_typecast(e, type);
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
      if(type.subtype()!=e.type().subtype())
        return false;

      struct_typet from_struct = to_struct_type(
        follow(static_cast<const typet &>(e.type().find(ID_to_member))));

      struct_typet to_struct = to_struct_type(
        follow(static_cast<const typet &>(type.find(ID_to_member))));

      if(subtype_typecast(from_struct, to_struct))
      {
        new_expr=e;
        new_expr.make_typecast(type);
        return true;
      }
    }
    else if(
      type.find(ID_to_member).is_nil() &&
      e.type().find(ID_to_member).is_not_nil())
    {
      if(type.subtype() != e.type().subtype())
        return false;

      struct_typet from_struct = to_struct_type(
        follow(static_cast<const typet &>(e.type().find(ID_to_member))));

      new_expr = e;
      new_expr.type().add(ID_to_member) = from_struct;

      return true;
    }
    else
      return false;
  }

  return false;
}
