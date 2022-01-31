/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include "expr2java.h"

#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/unicode.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>

#include <ansi-c/c_misc.h>
#include <ansi-c/expr2c_class.h>

#include "java_expr.h"
#include "java_qualifiers.h"
#include "java_string_literal_expr.h"
#include "java_types.h"

std::string expr2javat::convert(const typet &src)
{
  return convert_rec(src, java_qualifierst(ns), "");
}

std::string expr2javat::convert(const exprt &src)
{
  return expr2ct::convert(src);
}

std::string expr2javat::convert_code_function_call(
  const code_function_callt &src,
  unsigned indent)
{
  if(src.operands().size()!=3)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  std::string dest=indent_str(indent);

  if(src.lhs().is_not_nil())
  {
    unsigned p;
    std::string lhs_str=convert_with_precedence(src.lhs(), p);

    dest+=lhs_str;
    dest+='=';
  }

  const java_method_typet &method_type =
    to_java_method_type(src.function().type());

  bool has_this = method_type.has_this() && !src.arguments().empty();

  if(has_this)
  {
    unsigned p;
    std::string this_str=convert_with_precedence(src.arguments()[0], p);
    dest+=this_str;
    dest+=" . "; // extra spaces for readability
  }

  {
    unsigned p;
    std::string function_str=convert_with_precedence(src.function(), p);
    dest+=function_str;
  }

  dest+='(';

  const exprt::operandst &arguments=src.arguments();

  bool first=true;

  forall_expr(it, arguments)
  {
    if(has_this && it==arguments.begin())
    {
    }
    else
    {
      unsigned p;
      std::string arg_str=convert_with_precedence(*it, p);

      if(first)
        first=false;
      else
        dest+=", ";
      dest+=arg_str;
    }
  }

  dest+=");";

  return dest;
}

std::string expr2javat::convert_struct(
  const exprt &src,
  unsigned &precedence)
{
  const typet &full_type=ns.follow(src.type());

  if(full_type.id()!=ID_struct)
    return convert_norep(src, precedence);

  const struct_typet &struct_type=to_struct_type(full_type);

  std::string dest="{ ";

  const struct_typet::componentst &components=
    struct_type.components();

  assert(components.size()==src.operands().size());

  exprt::operandst::const_iterator o_it=src.operands().begin();

  bool first=true;
  size_t last_size=0;

  for(const auto &c : components)
  {
    if(c.type().id() != ID_code)
    {
      std::string tmp=convert(*o_it);
      std::string sep;

      if(first)
        first=false;
      else
      {
        if(last_size+40<dest.size())
        {
          sep=",\n    ";
          last_size=dest.size();
        }
        else
          sep=", ";
      }

      dest+=sep;
      dest+='.';
      irep_idt field_name = c.get_pretty_name();
      if(field_name.empty())
        field_name = c.get_name();
      dest += id2string(field_name);
      dest+='=';
      dest+=tmp;
    }

    o_it++;
  }

  dest+=" }";

  return dest;
}

std::string expr2javat::convert_constant(
  const constant_exprt &src,
  unsigned &precedence)
{
  if(src.type().id()==ID_c_bool)
  {
    if(!src.is_zero())
      return "true";
    else
      return "false";
  }
  else if(src.type().id()==ID_bool)
  {
    if(src.is_true())
      return "true";
    else if(src.is_false())
      return "false";
  }
  else if(src.type().id()==ID_pointer)
  {
    // Java writes 'null' for the null reference
    if(src.is_zero())
      return "null";
  }
  else if(src.type()==java_char_type())
  {
    std::string dest;
    dest.reserve(char_representation_length);

    const char16_t int_value = numeric_cast_v<char16_t>(src);

    // Character literals in Java have type 'char', thus no cast is needed.
    // This is different from C, where charater literals have type 'int'.
    dest += '\'' + utf16_native_endian_to_java(int_value) + '\'';
    return dest;
  }
  else if(src.type()==java_byte_type())
  {
    // No byte-literals in Java, so just cast:
    const mp_integer int_value = numeric_cast_v<mp_integer>(src);
    std::string dest="(byte)";
    dest+=integer2string(int_value);
    return dest;
  }
  else if(src.type()==java_short_type())
  {
    // No short-literals in Java, so just cast:
    const mp_integer int_value = numeric_cast_v<mp_integer>(src);
    std::string dest="(short)";
    dest+=integer2string(int_value);
    return dest;
  }
  else if(src.type()==java_long_type())
  {
    // long integer literals must have 'L' at the end
    const mp_integer int_value = numeric_cast_v<mp_integer>(src);
    std::string dest=integer2string(int_value);
    dest+='L';
    return dest;
  }
  else if((src.type()==java_float_type()) ||
          (src.type()==java_double_type()))
  {
    // This converts NaNs to the canonical NaN
    const ieee_floatt ieee_repr(to_constant_expr(src));
    if(ieee_repr.is_double())
      return floating_point_to_java_string(ieee_repr.to_double());
    return floating_point_to_java_string(ieee_repr.to_float());
  }


  return expr2ct::convert_constant(src, precedence);
}

std::string expr2javat::convert_rec(
  const typet &src,
  const qualifierst &qualifiers,
  const std::string &declarator)
{
  std::unique_ptr<qualifierst> clone = qualifiers.clone();
  qualifierst &new_qualifiers = *clone;
  new_qualifiers.read(src);

  const std::string d = declarator.empty() ? declarator : (" " + declarator);

  const std::string q=
    new_qualifiers.as_string();

  if(src==java_int_type())
    return q+"int"+d;
  else if(src==java_long_type())
    return q+"long"+d;
  else if(src==java_short_type())
    return q+"short"+d;
  else if(src==java_byte_type())
    return q+"byte"+d;
  else if(src==java_char_type())
    return q+"char"+d;
  else if(src==java_float_type())
    return q+"float"+d;
  else if(src==java_double_type())
    return q+"double"+d;
  else if(src==java_boolean_type())
    return q+"boolean"+d;
  else if(src==java_byte_type())
    return q+"byte"+d;
  else if(src.id()==ID_code)
  {
    const java_method_typet &method_type = to_java_method_type(src);

    // Java doesn't really have syntax for function types,
    // so we make one up, loosely inspired by the syntax
    // of lambda expressions.

    std::string dest;

    dest+='(';
    const java_method_typet::parameterst &parameters = method_type.parameters();

    for(java_method_typet::parameterst::const_iterator it = parameters.begin();
        it != parameters.end();
        it++)
    {
      if(it!=parameters.begin())
        dest+=", ";

      dest+=convert(it->type());
    }

    if(method_type.has_ellipsis())
    {
      if(!parameters.empty())
        dest+=", ";
      dest+="...";
    }

    dest+=')';

    const typet &return_type = method_type.return_type();
    dest+=" -> "+convert(return_type);

    return q + dest;
  }
  else
    return expr2ct::convert_rec(src, qualifiers, declarator);
}

std::string expr2javat::convert_java_this()
{
  return id2string(ID_this);
}

std::string expr2javat::convert_java_instanceof(const exprt &src)
{
  const auto &instanceof_expr = to_java_instanceof_expr(src);

  return convert(instanceof_expr.tested_expr()) + " instanceof " +
         convert(instanceof_expr.target_type());
}

std::string expr2javat::convert_code_java_new(const exprt &src, unsigned indent)
{
  return indent_str(indent) + convert_java_new(src) + ";\n";
}

std::string expr2javat::convert_java_new(const exprt &src)
{
  std::string dest;

  if(src.get(ID_statement)==ID_java_new_array ||
     src.get(ID_statement)==ID_java_new_array_data)
  {
    dest="new";

    std::string tmp_size=
      convert(static_cast<const exprt &>(src.find(ID_size)));

    dest+=' ';
    dest += convert(to_pointer_type(src.type()).base_type());
    dest+='[';
    dest+=tmp_size;
    dest+=']';
  }
  else
    dest = "new " + convert(to_pointer_type(src.type()).base_type());

  return dest;
}

std::string expr2javat::convert_code_java_delete(
  const exprt &src,
  unsigned indent)
{
  std::string dest=indent_str(indent)+"delete ";

  if(src.operands().size()!=1)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  std::string tmp = convert(to_unary_expr(src).op());

  dest+=tmp+";\n";

  return dest;
}

std::string expr2javat::convert_with_precedence(
  const exprt &src,
  unsigned &precedence)
{
  if(src.id()=="java-this")
  {
    precedence = 15;
    return convert_java_this();
  }
  if(src.id()==ID_java_instanceof)
  {
    precedence = 15;
    return convert_java_instanceof(src);
  }
  else if(src.id()==ID_side_effect &&
          (src.get(ID_statement)==ID_java_new ||
           src.get(ID_statement)==ID_java_new_array ||
           src.get(ID_statement)==ID_java_new_array_data))
  {
    precedence = 15;
    return convert_java_new(src);
  }
  else if(src.id()==ID_side_effect &&
          src.get(ID_statement)==ID_throw)
  {
    precedence = 16;
    return convert_function(src, "throw");
  }
  else if(src.id()==ID_code &&
          to_code(src).get_statement()==ID_exception_landingpad)
  {
    const exprt &catch_expr=
      to_code_landingpad(to_code(src)).catch_expr();
    return "catch_landingpad("+
      convert(catch_expr.type())+
      ' '+
      convert(catch_expr)+
      ')';
  }
  else if(src.id()==ID_unassigned)
    return "?";
  else if(src.id()=="pod_constructor")
    return "pod_constructor";
  else if(src.id()==ID_virtual_function)
  {
    const class_method_descriptor_exprt &virtual_function =
      to_class_method_descriptor_expr(src);
    return "CLASS_METHOD_DESCRIPTOR(" + id2string(virtual_function.class_id()) +
           "." + id2string(virtual_function.mangled_method_name()) + ")";
  }
  else if(
    const auto &literal = expr_try_dynamic_cast<java_string_literal_exprt>(src))
  {
    return '"' + MetaString(id2string(literal->value())) + '"';
  }
  else if(src.id()==ID_constant)
    return convert_constant(to_constant_expr(src), precedence=16);
  else
    return expr2ct::convert_with_precedence(src, precedence);
}

std::string expr2javat::convert_code(
  const codet &src,
  unsigned indent)
{
  const irep_idt &statement=src.get(ID_statement);

  if(statement==ID_java_new ||
     statement==ID_java_new_array)
    return convert_code_java_new(src, indent);

  if(statement==ID_function_call)
    return convert_code_function_call(to_code_function_call(src), indent);

  return expr2ct::convert_code(src, indent);
}

std::string expr2java(const exprt &expr, const namespacet &ns)
{
  expr2javat expr2java(ns);
  expr2java.get_shorthands(expr);
  return expr2java.convert(expr);
}

std::string type2java(const typet &type, const namespacet &ns)
{
  expr2javat expr2java(ns);
  return expr2java.convert(type);
}
