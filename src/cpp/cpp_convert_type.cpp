/*******************************************************************\

Module: C++ Language Type Conversion

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Conversion

#include "cpp_convert_type.h"

#include <util/c_types.h>
#include <util/config.h>
#include <util/invariant.h>
#include <util/std_types.h>

#include <ansi-c/ansi_c_convert_type.h>

#include "cpp_declaration.h"
#include "cpp_name.h"

class cpp_convert_typet : public ansi_c_convert_typet
{
public:
  // The following types exist in C11 and later, but are implemented as
  // typedefs. In C++, they are keywords and thus required explicit handling in
  // here.
  std::size_t wchar_t_count, char16_t_count, char32_t_count;

  void write(typet &type) override;

  cpp_convert_typet(message_handlert &message_handler, const typet &type)
    : ansi_c_convert_typet(message_handler)
  {
    read(type);
  }

protected:
  void clear() override
  {
    wchar_t_count = 0;
    char16_t_count = 0;
    char32_t_count = 0;

    ansi_c_convert_typet::clear();
  }

  void read_rec(const typet &type) override;
  void read_function_type(const typet &type);
  void read_template(const typet &type);
};

void cpp_convert_typet::read_rec(const typet &type)
{
  #if 0
  std::cout << "cpp_convert_typet::read_rec: "
            << type.pretty() << '\n';
  #endif

  if(type.id() == ID_gcc_float80)
    ++gcc_float64x_cnt;
  else if(type.id()==ID_wchar_t)
    ++wchar_t_count;
  else if(type.id()==ID_char16_t)
    ++char16_t_count;
  else if(type.id()==ID_char32_t)
    ++char32_t_count;
  else if(type.id()==ID_constexpr)
    c_qualifiers.is_constant = true;
  else if(type.id()==ID_function_type)
  {
    read_function_type(type);
  }
  else if(type.id()==ID_identifier)
  {
    // from parameters
  }
  else if(type.id()==ID_cpp_name)
  {
    // from typedefs
    other.push_back(type);
  }
  else if(type.id()==ID_array)
  {
    other.push_back(type);
    cpp_convert_plain_type(other.back().subtype(), get_message_handler());
  }
  else if(type.id()==ID_template)
  {
    read_template(type);
  }
  else if(type.id()==ID_frontend_pointer)
  {
    // add width and turn into ID_pointer
    pointer_typet tmp(
      to_type_with_subtype(type).subtype(), config.ansi_c.pointer_width);
    tmp.add_source_location()=type.source_location();
    if(type.get_bool(ID_C_reference))
      tmp.set(ID_C_reference, true);
    if(type.get_bool(ID_C_rvalue_reference))
      tmp.set(ID_C_rvalue_reference, true);
    const irep_idt typedef_identifier = type.get(ID_C_typedef);
    if(!typedef_identifier.empty())
      tmp.set(ID_C_typedef, typedef_identifier);
    other.push_back(tmp);
  }
  else if(type.id()==ID_pointer)
  {
    // ignore, we unfortunately convert multiple times
    other.push_back(type);
  }
  else if(type.id() == ID_frontend_vector)
    vector_size = static_cast<const exprt &>(type.find(ID_size));
  else
  {
    ansi_c_convert_typet::read_rec(type);
  }
}

void cpp_convert_typet::read_template(const typet &type)
{
  other.push_back(type);
  typet &t=other.back();

  cpp_convert_plain_type(t.subtype(), get_message_handler());

  irept &arguments=t.add(ID_arguments);

  for(auto &argument : arguments.get_sub())
  {
    exprt &decl = static_cast<exprt &>(argument);

    // may be type or expression
    bool is_type=decl.get_bool(ID_is_type);

    if(is_type)
    {
    }
    else
    {
      cpp_convert_plain_type(decl.type(), get_message_handler());
    }

    // TODO: initializer
  }
}

void cpp_convert_typet::read_function_type(const typet &type)
{
  other.push_back(type);
  other.back().id(ID_code);

  code_typet &t = to_code_type(other.back());

  // change subtype to return_type
  typet &return_type = t.return_type();

  return_type.swap(t.subtype());
  t.remove_subtype();

  if(return_type.is_not_nil())
    cpp_convert_plain_type(return_type, get_message_handler());

  // take care of parameter types
  code_typet::parameterst &parameters = t.parameters();

  // see if we have an ellipsis
  if(!parameters.empty() && parameters.back().id() == ID_ellipsis)
  {
    t.make_ellipsis();
    parameters.pop_back();
  }

  for(auto &parameter_expr : parameters)
  {
    if(parameter_expr.id()==ID_cpp_declaration)
    {
      cpp_declarationt &declaration=to_cpp_declaration(parameter_expr);
      source_locationt type_location=declaration.type().source_location();

      cpp_convert_plain_type(declaration.type(), get_message_handler());

      // there should be only one declarator
      assert(declaration.declarators().size()==1);

      cpp_declaratort &declarator=
        declaration.declarators().front();

      // do we have a declarator?
      if(declarator.is_nil())
      {
        parameter_expr = code_typet::parametert(declaration.type());
        parameter_expr.add_source_location()=type_location;
      }
      else
      {
        const cpp_namet &cpp_name=declarator.name();
        typet final_type=declarator.merge_type(declaration.type());

        // see if it's an array type
        if(final_type.id()==ID_array)
        {
          // turn into pointer type
          final_type=pointer_type(final_type.subtype());
        }

        code_typet::parametert new_parameter(final_type);

        if(cpp_name.is_nil())
        {
          new_parameter.add_source_location()=type_location;
        }
        else if(cpp_name.is_simple_name())
        {
          irep_idt base_name=cpp_name.get_base_name();
          assert(!base_name.empty());
          new_parameter.set_identifier(base_name);
          new_parameter.set_base_name(base_name);
          new_parameter.add_source_location()=cpp_name.source_location();
        }
        else
        {
          throw "expected simple name as parameter";
        }

        if(declarator.value().is_not_nil())
          new_parameter.default_value().swap(declarator.value());

        parameter_expr.swap(new_parameter);
      }
    }
    else if(parameter_expr.id()==ID_ellipsis)
    {
      throw "ellipsis only allowed as last parameter";
    }
    else
      UNREACHABLE;
  }

  // if we just have one parameter of type void, remove it
  if(parameters.size() == 1 && parameters.front().type().id() == ID_empty)
    parameters.clear();
}

void cpp_convert_typet::write(typet &type)
{
  if(!other.empty())
  {
    if(wchar_t_count || char16_t_count || char32_t_count)
    {
      error().source_location = source_location;
      error() << "illegal type modifier for defined type" << eom;
      throw 0;
    }

    ansi_c_convert_typet::write(type);
  }
  else if(c_bool_cnt)
  {
    if(
      signed_cnt || unsigned_cnt || int_cnt || short_cnt || char_cnt ||
      wchar_t_count || proper_bool_cnt || char16_t_count || char32_t_count ||
      int8_cnt || int16_cnt || int32_cnt || int64_cnt || gcc_int128_cnt ||
      ptr32_cnt || ptr64_cnt)
    {
      throw "illegal type modifier for C++ bool";
    }

    ansi_c_convert_typet::write(type);
  }
  else if(wchar_t_count)
  {
    // This is a distinct type, and can't be made signed/unsigned.
    // This is tolerated by most compilers, however.

    if(
      int_cnt || short_cnt || char_cnt || long_cnt || char16_t_count ||
      char32_t_count || int8_cnt || int16_cnt || int32_cnt || int64_cnt ||
      ptr32_cnt || ptr64_cnt)
    {
      throw "illegal type modifier for wchar_t";
    }

    type=wchar_t_type();
    ansi_c_convert_typet::build_type_with_subtype(type);
    ansi_c_convert_typet::set_attributes(type);
  }
  else if(char16_t_count)
  {
    // This is a distinct type, and can't be made signed/unsigned.
    if(
      int_cnt || short_cnt || char_cnt || long_cnt || char32_t_count ||
      int8_cnt || int16_cnt || int32_cnt || int64_cnt || ptr32_cnt ||
      ptr64_cnt || signed_cnt || unsigned_cnt)
    {
      throw "illegal type modifier for char16_t";
    }

    type=char16_t_type();
    ansi_c_convert_typet::build_type_with_subtype(type);
    ansi_c_convert_typet::set_attributes(type);
  }
  else if(char32_t_count)
  {
    // This is a distinct type, and can't be made signed/unsigned.
    if(int_cnt || short_cnt || char_cnt || long_cnt ||
       int8_cnt || int16_cnt || int32_cnt ||
       int64_cnt || ptr32_cnt || ptr64_cnt ||
       signed_cnt || unsigned_cnt)
    {
      throw "illegal type modifier for char32_t";
    }

    type=char32_t_type();
    ansi_c_convert_typet::build_type_with_subtype(type);
    ansi_c_convert_typet::set_attributes(type);
  }
  else
  {
    ansi_c_convert_typet::write(type);
  }
}

void cpp_convert_plain_type(typet &type, message_handlert &message_handler)
{
  if(
    type.id() == ID_cpp_name || type.id() == ID_struct ||
    type.id() == ID_union || type.id() == ID_array || type.id() == ID_code ||
    type.id() == ID_unsignedbv || type.id() == ID_signedbv ||
    type.id() == ID_bool || type.id() == ID_floatbv || type.id() == ID_empty ||
    type.id() == ID_constructor || type.id() == ID_destructor)
  {
  }
  else if(type.id()==ID_c_enum)
  {
    // add width -- we use int, but the standard
    // doesn't guarantee that
    type.set(ID_width, config.ansi_c.int_width);
  }
  else if(type.id() == ID_c_bool)
  {
    type.set(ID_width, config.ansi_c.bool_width);
  }
  else
  {
    cpp_convert_typet cpp_convert_type(message_handler, type);
    cpp_convert_type.write(type);
  }
}

void cpp_convert_auto(
  typet &dest,
  const typet &src,
  message_handlert &message_handler)
{
  if(dest.id() != ID_merged_type && dest.has_subtype())
  {
    cpp_convert_auto(dest.subtype(), src, message_handler);
    return;
  }

  cpp_convert_typet cpp_convert_type(message_handler, dest);
  for(auto &t : cpp_convert_type.other)
    if(t.id() == ID_auto)
      t = src;

  cpp_convert_type.write(dest);
}
