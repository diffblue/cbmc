/*******************************************************************\

Module: C++ Language Type Conversion

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <assert.h>

#include <iostream>

#include <config.h>
#include <arith_tools.h>
#include <std_types.h>

#include <ansi-c/c_types.h>

#include "cpp_convert_type.h"
#include "cpp_declaration.h"
#include "cpp_name.h"

class cpp_convert_typet
{
public:
  unsigned unsigned_cnt, signed_cnt, char_cnt, int_cnt, short_cnt,
           long_cnt, const_cnt, typedef_cnt, volatile_cnt,
           double_cnt, float_cnt, complex_cnt, cpp_bool_cnt, proper_bool_cnt,
           extern_cnt, wchar_t_cnt,
           int8_cnt, int16_cnt, int32_cnt, int64_cnt, ptr32_cnt, ptr64_cnt,
           float128_cnt, int128_cnt;

  void read(const typet &type);
  void write(typet &type);

  std::list<typet> other;

  cpp_convert_typet() { }
  cpp_convert_typet(const typet &type) { read(type); }

protected:
  void read_rec(const typet &type);
  void read_function_type(const typet &type);
  void read_template(const typet &type);
};

/*******************************************************************\

Function: cpp_convert_typet::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_convert_typet::read(const typet &type)
{
  unsigned_cnt=signed_cnt=char_cnt=int_cnt=short_cnt=
  long_cnt=const_cnt=typedef_cnt=volatile_cnt=
  double_cnt=float_cnt=complex_cnt=cpp_bool_cnt=proper_bool_cnt=
  extern_cnt=wchar_t_cnt=int8_cnt=int16_cnt=int32_cnt=
  int64_cnt=ptr32_cnt=ptr64_cnt=float128_cnt=int128_cnt=0;

  other.clear();
  
  #if 0
  std::cout << "cpp_convert_typet::read: " << type.pretty() << std::endl;
  #endif

  read_rec(type);
}

/*******************************************************************\

Function: cpp_convert_typet::read_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_convert_typet::read_rec(const typet &type)
{
  #if 0
  std::cout << "cpp_convert_typet::read_rec: "
            << type.pretty() << std::endl;
  #endif

  if(type.id()==ID_merged_type)
  {
    forall_subtypes(it, type)
      read_rec(*it);
  }
  else if(type.id()==ID_signed)
    signed_cnt++;
  else if(type.id()==ID_unsigned)
    unsigned_cnt++;
  else if(type.id()==ID_volatile)
    volatile_cnt++;
  else if(type.id()==ID_char)
    char_cnt++;
  else if(type.id()==ID_int)
    int_cnt++;
  else if(type.id()==ID_short)
    short_cnt++;
  else if(type.id()==ID_long)
    long_cnt++;
  else if(type.id()==ID_double)
    double_cnt++;
  else if(type.id()==ID_float)
    float_cnt++;
  else if(type.id()=="__float128")
    float128_cnt++;
  else if(type.id()=="__int128")
    int128_cnt++;
  else if(type.id()=="__complex__" || type.id()=="_Complex")
    complex_cnt++;
  else if(type.id()==ID_bool)
    cpp_bool_cnt++;
  else if(type.id()=="__CPROVER_bool")
    proper_bool_cnt++;
  else if(type.id()==ID_wchar_t)
    wchar_t_cnt++;
  else if(type.id()=="__int8")
    int8_cnt++;
  else if(type.id()=="__int16")
    int16_cnt++;
  else if(type.id()=="__int32")
    int32_cnt++;
  else if(type.id()=="__int64")
    int64_cnt++;
  else if(type.id()=="__ptr32")
    ptr32_cnt++;
  else if(type.id()=="__ptr64")
    ptr64_cnt++;
  else if(type.id()==ID_const)
    const_cnt++;
  else if(type.id()==ID_extern)
    extern_cnt++;
  else if(type.id()=="function_type")
  {
    read_function_type(type);
  }
  else if(type.id()==ID_typedef)
    typedef_cnt++;
  else if(type.id()==ID_identifier)
  {
    // from arguments
  }
  else if(type.id()==ID_cpp_name)
  {
    // from typedefs
    other.push_back(type);
  }
  else if(type.id()==ID_array)
  {
    other.push_back(type);
    cpp_convert_plain_type(other.back().subtype());
  }
  else if(type.id()==ID_template)
  {
    read_template(type);
  }
  else if(type.id()==ID_void)
  {
    // we store 'void' as 'empty'
    typet tmp=type;
    tmp.id(ID_empty);
    other.push_back(tmp);
  }
  else
  {
    other.push_back(type);
  }
}

/*******************************************************************\

Function: cpp_covnert_typet::read_template

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_convert_typet::read_template(const typet &type)
{
  other.push_back(type);
  typet &t=other.back();

  cpp_convert_plain_type(t.subtype());

  irept &arguments=t.add(ID_arguments);

  Forall_irep(it, arguments.get_sub())
  {
    exprt &decl=static_cast<exprt &>(*it);

    // may be type or expression
    bool is_type=decl.get_bool(ID_is_type);

    if(is_type)
    {
    }
    else
    {
      cpp_convert_plain_type(decl.type());
    }

    // TODO: initializer
  }
}

/*******************************************************************\

Function: cpp_convert_typet::read_function_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_convert_typet::read_function_type(const typet &type)
{
  other.push_back(type);
  typet &t=other.back();
  t.id(ID_code);

  // change subtype to return_type
  typet &return_type=
    static_cast<typet &>(t.add(ID_return_type));

  return_type.swap(t.subtype());
  t.remove(ID_subtype);

  if(return_type.is_not_nil())
    cpp_convert_plain_type(return_type);

  // take care of argument types
  irept &arguments=t.add(ID_arguments);

  // see if we have an ellipsis
  if(!arguments.get_sub().empty() &&
     arguments.get_sub().back().id()==ID_ellipsis)
  {
    arguments.set(ID_ellipsis, true);
    arguments.get_sub().erase(--arguments.get_sub().end());
  }

  Forall_irep(it, arguments.get_sub())
  {
    exprt &argument_expr=static_cast<exprt &>(*it);

    if(argument_expr.id()==ID_cpp_declaration)
    {
      cpp_declarationt &declaration=to_cpp_declaration(argument_expr);
      locationt type_location=declaration.type().location();

      cpp_convert_plain_type(declaration.type());

      // there should be only one declarator
      assert(declaration.declarators().size()==1);

      cpp_declaratort &declarator=
        declaration.declarators().front();

      // do we have a declarator?
      if(declarator.is_nil())
      {
        argument_expr=exprt(ID_argument, declaration.type());
        argument_expr.location()=type_location;
      }
      else
      {
        const cpp_namet &cpp_name=declarator.name();
        typet final_type=declarator.merge_type(declaration.type());

        // see if it's an array type
        if(final_type.id()==ID_array)
        {
          final_type.id(ID_pointer);
          final_type.remove(ID_size);
        }

        code_typet::argumentt new_argument(final_type);

        if(cpp_name.is_nil())
        {
          new_argument.location()=type_location;
        }
        else if(cpp_name.is_simple_name())
        {
          irep_idt base_name=cpp_name.get_base_name();
          assert(!base_name.empty());
          new_argument.set_identifier(base_name);
          new_argument.set_base_name(base_name);
          new_argument.location()=cpp_name.location();
        }
        else
        {
          throw "expected simple name as argument";
        }

        if(declarator.value().is_not_nil())
          new_argument.default_value().swap(declarator.value());

        argument_expr.swap(new_argument);
      }
    }
    else if(argument_expr.id()==ID_ellipsis)
    {
      throw "ellipsis only allowed as last argument";
    }
    else
      assert(false);
  }

  // if we just have one argument of type void, remove it
  if(arguments.get_sub().size()==1 &&
     arguments.get_sub().front().find(ID_type).id()==ID_empty)
    arguments.get_sub().clear();
}

/*******************************************************************\

Function: cpp_convert_typet::write

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_convert_typet::write(typet &type)
{
  type.clear();
  
  // first, do "other"
  
  if(!other.empty())
  {
    if(double_cnt || float_cnt || signed_cnt ||
       unsigned_cnt || int_cnt || cpp_bool_cnt || proper_bool_cnt ||
       short_cnt || char_cnt || wchar_t_cnt ||
       int8_cnt || int16_cnt || int32_cnt ||
       int64_cnt || float128_cnt || int128_cnt)
      throw "type modifier not applicable";

    if(other.size()!=1)
      throw "illegal combination of types";

    type.swap(other.front());
  }
  else if(double_cnt)
  {
    if(signed_cnt || unsigned_cnt || int_cnt ||
       cpp_bool_cnt || proper_bool_cnt ||
       short_cnt || char_cnt || wchar_t_cnt || float_cnt ||
       int8_cnt || int16_cnt || int32_cnt ||
       int64_cnt || ptr32_cnt || ptr64_cnt ||
       float128_cnt || int128_cnt)
      throw "illegal type modifier for double";

    if(long_cnt)
      type=long_double_type();
    else
      type=double_type();
  }
  else if(float_cnt)
  {
    if(signed_cnt || unsigned_cnt || int_cnt ||
       cpp_bool_cnt || proper_bool_cnt ||
       short_cnt || char_cnt || wchar_t_cnt || double_cnt ||
       int8_cnt || int16_cnt || int32_cnt ||
       int64_cnt || ptr32_cnt || ptr64_cnt || float128_cnt || int128_cnt)
      throw "illegal type modifier for float";

    if(long_cnt)
      throw "float can't be long";

    type=float_type();
  }
  else if(float128_cnt)
  {
    if(signed_cnt || unsigned_cnt || int_cnt ||
       cpp_bool_cnt || proper_bool_cnt ||
       short_cnt || char_cnt || wchar_t_cnt || double_cnt ||
       int8_cnt || int16_cnt || int32_cnt ||
       int64_cnt || int128_cnt || ptr32_cnt || ptr64_cnt)
      throw "illegal type modifier for __float128";

    if(long_cnt)
      throw "__float128 can't be long";

    // this isn't the same as long double
    type=gcc_float128_type();
  }
  else if(cpp_bool_cnt)
  {
    if(signed_cnt || unsigned_cnt || int_cnt || short_cnt ||
       char_cnt || wchar_t_cnt || proper_bool_cnt ||
       int8_cnt || int16_cnt || int32_cnt ||
       int64_cnt || int128_cnt || ptr32_cnt || ptr64_cnt)
      throw "illegal type modifier for C++ bool";

    type.id(ID_bool);
  }
  else if(proper_bool_cnt)
  {
    if(signed_cnt || unsigned_cnt || int_cnt || short_cnt ||
       char_cnt || wchar_t_cnt ||
       int8_cnt || int16_cnt || int32_cnt ||
       int64_cnt || int128_cnt || ptr32_cnt || ptr64_cnt)
      throw "illegal type modifier for __CPROVER_bool";

    type.id(ID_bool);
  }
  else if(char_cnt)
  {
    if(int_cnt || short_cnt || wchar_t_cnt || long_cnt ||
       int8_cnt || int16_cnt || int32_cnt ||
       int64_cnt || int128_cnt || ptr32_cnt || ptr64_cnt)
      throw "illegal type modifier for char";

    // there are really three distinct char types in C++
    if(unsigned_cnt)
      type=unsigned_char_type();
    else if(signed_cnt)
      type=signed_char_type();
    else
      type=char_type();
  }
  else if(wchar_t_cnt)
  {
    // This is a distinct type, and can't be made signed/unsigned.
    // This is tolerated by most compilers, however.

    if(int_cnt || short_cnt || char_cnt || long_cnt ||
       int8_cnt || int16_cnt || int32_cnt ||
       int64_cnt || ptr32_cnt || ptr64_cnt)
      throw "illegal type modifier for wchar_t";

    type=wchar_t_type();
  }
  else
  {
    // it must be integer -- signed or unsigned?

    if(signed_cnt && unsigned_cnt)
      throw "integer cannot be both signed and unsigned";

    if(short_cnt)
    {
      if(long_cnt)
        throw "cannot combine short and long";

      if(unsigned_cnt)
        type=unsigned_short_int_type();
      else
        type=signed_short_int_type();
    }
    else if(int8_cnt)
    {
      if(long_cnt)
        throw "illegal type modifier for __int8";

      // in terms of overloading, this behaves like "char"
      if(unsigned_cnt)
        type=unsigned_char_type();
      else if(signed_cnt)
        type=signed_char_type();
      else
        type=char_type(); // check?
    }
    else if(int16_cnt)
    {
      if(long_cnt)
        throw "illegal type modifier for __int16";

      // in terms of overloading, this behaves like "short"
      if(unsigned_cnt)
        type=unsigned_short_int_type();
      else
        type=signed_short_int_type();
    }
    else if(int32_cnt)
    {
      if(long_cnt)
        throw "illegal type modifier for __int32";

      // in terms of overloading, this behaves like "int"
      if(unsigned_cnt)
        type=unsigned_int_type();
      else
        type=signed_int_type();
    }
    else if(int64_cnt)
    {
      if(long_cnt)
        throw "illegal type modifier for __int64";

      // in terms of overloading, this behaves like "long long"
      if(unsigned_cnt)
        type=unsigned_long_long_int_type();
      else
        type=signed_long_long_int_type();
    }
    else if(int128_cnt)
    {
      if(long_cnt)
        throw "illegal type modifier for __int128";

      if(unsigned_cnt)
        type=gcc_unsigned_int128_type();
      else
        type=gcc_signed_int128_type();
    }
    else if(long_cnt==0)
    {
      if(unsigned_cnt)
        type=unsigned_int_type();
      else
        type=signed_int_type();
    }
    else if(long_cnt==1)
    {
      if(unsigned_cnt)
        type=unsigned_long_int_type();
      else
        type=signed_long_int_type();
    }
    else if(long_cnt==2)
    {
      if(unsigned_cnt)
        type=unsigned_long_long_int_type();
      else
        type=signed_long_long_int_type();
    }
    else
      throw "illegal combination of type modifiers";
  }

  // is it constant?
  if(const_cnt)
    type.set(ID_C_constant, true);

  // is it volatile?
  if(volatile_cnt)
    type.set(ID_C_volatile, true);
}

/*******************************************************************\

Function: cpp_convert_plain_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_convert_plain_type(typet &type)
{
  if(type.id()==ID_cpp_name ||
     type.id()==ID_struct ||
     type.id()==ID_union ||
     type.id()==ID_pointer ||
     type.id()==ID_array ||
     type.id()==ID_code ||
     type.id()==ID_unsignedbv ||
     type.id()==ID_signedbv ||
     type.id()==ID_bool ||
     type.id()==ID_floatbv ||
     type.id()==ID_empty ||
     type.id()==ID_symbol ||
     type.id()==ID_constructor ||
     type.id()==ID_destructor)
  {
  }
  else if(type.id()==ID_c_enum)
  {
    // add width -- we use int, but the standard
    // doesn't guarantee that
    type.set(ID_width, config.ansi_c.int_width);
  }
  else
  {
    cpp_convert_typet cpp_convert_type(type);
    cpp_convert_type.write(type);
  }
}
