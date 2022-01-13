/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "c_typecheck_base.h"

#include <unordered_set>

#include <goto-programs/goto_instruction_code.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/fresh_symbol.h>
#include <util/mathematical_types.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>

#include "ansi_c_convert_type.h"
#include "ansi_c_declaration.h"
#include "c_qualifiers.h"
#include "gcc_types.h"
#include "padding.h"
#include "type2name.h"
#include "typedef_type.h"

void c_typecheck_baset::typecheck_type(typet &type)
{
  // we first convert, and then check
  {
    ansi_c_convert_typet ansi_c_convert_type(get_message_handler());

    ansi_c_convert_type.read(type);
    ansi_c_convert_type.write(type);
  }

  if(type.id()==ID_already_typechecked)
  {
    already_typechecked_typet &already_typechecked =
      to_already_typechecked_type(type);

    // need to preserve any qualifiers
    c_qualifierst c_qualifiers(type);
    c_qualifiers += c_qualifierst(already_typechecked.get_type());
    bool packed=type.get_bool(ID_C_packed);
    exprt alignment=static_cast<const exprt &>(type.find(ID_C_alignment));
    irept _typedef=type.find(ID_C_typedef);

    type = already_typechecked.get_type();

    c_qualifiers.write(type);
    if(packed)
      type.set(ID_C_packed, true);
    if(alignment.is_not_nil())
      type.add(ID_C_alignment, alignment);
    if(_typedef.is_not_nil())
      type.add(ID_C_typedef, _typedef);

    return; // done
  }

  // do we have alignment?
  if(type.find(ID_C_alignment).is_not_nil())
  {
    exprt &alignment=static_cast<exprt &>(type.add(ID_C_alignment));
    if(alignment.id()!=ID_default)
    {
      typecheck_expr(alignment);
      make_constant(alignment);
    }
  }

  if(type.id()==ID_code)
    typecheck_code_type(to_code_type(type));
  else if(type.id()==ID_array)
    typecheck_array_type(to_array_type(type));
  else if(type.id()==ID_pointer)
  {
    typecheck_type(type.subtype());
    INVARIANT(
      to_bitvector_type(type).get_width() > 0, "pointers must have width");
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union)
    typecheck_compound_type(to_struct_union_type(type));
  else if(type.id()==ID_c_enum)
    typecheck_c_enum_type(type);
  else if(type.id()==ID_c_enum_tag)
    typecheck_c_enum_tag_type(to_c_enum_tag_type(type));
  else if(type.id()==ID_c_bit_field)
    typecheck_c_bit_field_type(to_c_bit_field_type(type));
  else if(type.id()==ID_typeof)
    typecheck_typeof_type(type);
  else if(type.id() == ID_typedef_type)
    typecheck_typedef_type(type);
  else if(type.id() == ID_struct_tag ||
          type.id() == ID_union_tag)
  {
    // nothing to do, these stay as is
  }
  else if(type.id()==ID_vector)
  {
    // already done
  }
  else if(type.id() == ID_frontend_vector)
  {
    typecheck_vector_type(type);
  }
  else if(type.id()==ID_custom_unsignedbv ||
          type.id()==ID_custom_signedbv ||
          type.id()==ID_custom_floatbv ||
          type.id()==ID_custom_fixedbv)
    typecheck_custom_type(type);
  else if(type.id()==ID_gcc_attribute_mode)
  {
    // get that mode
    const irep_idt gcc_attr_mode = type.get(ID_size);

    // A list of all modes is at
    // http://www.delorie.com/gnu/docs/gcc/gccint_53.html
    typecheck_type(type.subtype());

    typet underlying_type=type.subtype();

    // gcc allows this, but clang doesn't; it's a compiler hint only,
    // but we'll try to interpret it the GCC way
    if(underlying_type.id()==ID_c_enum_tag)
    {
      underlying_type=
        follow_tag(to_c_enum_tag_type(underlying_type)).subtype();

      assert(underlying_type.id()==ID_signedbv ||
             underlying_type.id()==ID_unsignedbv);
    }

    if(underlying_type.id()==ID_signedbv ||
       underlying_type.id()==ID_unsignedbv)
    {
      bool is_signed=underlying_type.id()==ID_signedbv;

      typet result;

      if(gcc_attr_mode == "__QI__") // 8 bits
      {
        if(is_signed)
          result=signed_char_type();
        else
          result=unsigned_char_type();
      }
      else if(gcc_attr_mode == "__byte__") // 8 bits
      {
        if(is_signed)
          result=signed_char_type();
        else
          result=unsigned_char_type();
      }
      else if(gcc_attr_mode == "__HI__") // 16 bits
      {
        if(is_signed)
          result=signed_short_int_type();
        else
          result=unsigned_short_int_type();
      }
      else if(gcc_attr_mode == "__SI__") // 32 bits
      {
        if(is_signed)
          result=signed_int_type();
        else
          result=unsigned_int_type();
      }
      else if(gcc_attr_mode == "__word__") // long int, we think
      {
        if(is_signed)
          result=signed_long_int_type();
        else
          result=unsigned_long_int_type();
      }
      else if(gcc_attr_mode == "__pointer__") // size_t/ssize_t, we think
      {
        if(is_signed)
          result=signed_size_type();
        else
          result=size_type();
      }
      else if(gcc_attr_mode == "__DI__") // 64 bits
      {
        if(config.ansi_c.long_int_width==64)
        {
          if(is_signed)
            result=signed_long_int_type();
          else
            result=unsigned_long_int_type();
        }
        else
        {
          assert(config.ansi_c.long_long_int_width==64);

          if(is_signed)
            result=signed_long_long_int_type();
          else
            result=unsigned_long_long_int_type();
        }
      }
      else if(gcc_attr_mode == "__TI__") // 128 bits
      {
        if(is_signed)
          result=gcc_signed_int128_type();
        else
          result=gcc_unsigned_int128_type();
      }
      else if(gcc_attr_mode == "__V2SI__") // vector of 2 ints, deprecated
      {
        if(is_signed)
          result=vector_typet(
            signed_int_type(),
            from_integer(2, size_type()));
        else
          result=vector_typet(
            unsigned_int_type(),
            from_integer(2, size_type()));
      }
      else if(gcc_attr_mode == "__V4SI__") // vector of 4 ints, deprecated
      {
        if(is_signed)
          result=vector_typet(
            signed_int_type(),
            from_integer(4, size_type()));
        else
          result=vector_typet(
            unsigned_int_type(),
            from_integer(4, size_type()));
      }
      else // give up, just use subtype
        result=type.subtype();

      // save the location
      result.add_source_location()=type.source_location();

      if(type.subtype().id()==ID_c_enum_tag)
      {
        const irep_idt &tag_name=
          to_c_enum_tag_type(type.subtype()).get_identifier();
        symbol_table.get_writeable_ref(tag_name).type.subtype()=result;
      }

      type=result;
    }
    else if(underlying_type.id()==ID_floatbv)
    {
      typet result;

      if(gcc_attr_mode == "__SF__") // 32 bits
        result=float_type();
      else if(gcc_attr_mode == "__DF__") // 64 bits
        result=double_type();
      else if(gcc_attr_mode == "__TF__") // 128 bits
        result=gcc_float128_type();
      else if(gcc_attr_mode == "__V2SF__") // deprecated vector of 2 floats
        result=vector_typet(float_type(), from_integer(2, size_type()));
      else if(gcc_attr_mode == "__V2DF__") // deprecated vector of 2 doubles
        result=vector_typet(double_type(), from_integer(2, size_type()));
      else if(gcc_attr_mode == "__V4SF__") // deprecated vector of 4 floats
        result=vector_typet(float_type(), from_integer(4, size_type()));
      else if(gcc_attr_mode == "__V4DF__") // deprecated vector of 4 doubles
        result=vector_typet(double_type(), from_integer(4, size_type()));
      else // give up, just use subtype
        result=type.subtype();

      // save the location
      result.add_source_location()=type.source_location();

      type=result;
    }
    else if(underlying_type.id()==ID_complex)
    {
      // gcc allows this, but clang doesn't -- see enums above
      typet result;

      if(gcc_attr_mode == "__SC__") // 32 bits
        result=float_type();
      else if(gcc_attr_mode == "__DC__") // 64 bits
        result=double_type();
      else if(gcc_attr_mode == "__TC__") // 128 bits
        result=gcc_float128_type();
      else // give up, just use subtype
        result=type.subtype();

      // save the location
      result.add_source_location()=type.source_location();

      type=complex_typet(result);
    }
    else
    {
      error().source_location=type.source_location();
      error() << "attribute mode '" << gcc_attr_mode
              << "' applied to inappropriate type '" << to_string(type) << "'"
              << eom;
      throw 0;
    }
  }

  // do a mild bit of rule checking

  if(type.get_bool(ID_C_restricted) &&
     type.id()!=ID_pointer &&
     type.id()!=ID_array)
  {
    error().source_location=type.source_location();
    error() << "only a pointer can be 'restrict'" << eom;
    throw 0;
  }
}

void c_typecheck_baset::typecheck_custom_type(typet &type)
{
  // they all have a width
  exprt size_expr=
    static_cast<const exprt &>(type.find(ID_size));

  typecheck_expr(size_expr);
  source_locationt source_location=size_expr.source_location();
  make_constant_index(size_expr);

  mp_integer size_int;
  if(to_integer(to_constant_expr(size_expr), size_int))
  {
    error().source_location=source_location;
    error() << "failed to convert bit vector width to constant" << eom;
    throw 0;
  }

  if(size_int<1)
  {
    error().source_location=source_location;
    error() << "bit vector width invalid" << eom;
    throw 0;
  }

  type.remove(ID_size);
  type.set(ID_width, integer2string(size_int));

  // depending on type, there may be a number of fractional bits

  if(type.id()==ID_custom_unsignedbv)
    type.id(ID_unsignedbv);
  else if(type.id()==ID_custom_signedbv)
    type.id(ID_signedbv);
  else if(type.id()==ID_custom_fixedbv)
  {
    type.id(ID_fixedbv);

    exprt f_expr=
      static_cast<const exprt &>(type.find(ID_f));

    const source_locationt fraction_source_location =
      f_expr.find_source_location();

    typecheck_expr(f_expr);

    make_constant_index(f_expr);

    mp_integer f_int;
    if(to_integer(to_constant_expr(f_expr), f_int))
    {
      error().source_location = fraction_source_location;
      error() << "failed to convert number of fraction bits to constant" << eom;
      throw 0;
    }

    if(f_int<0 || f_int>size_int)
    {
      error().source_location = fraction_source_location;
      error() << "fixedbv fraction width invalid" << eom;
      throw 0;
    }

    type.remove(ID_f);
    type.set(ID_integer_bits, integer2string(size_int-f_int));
  }
  else if(type.id()==ID_custom_floatbv)
  {
    type.id(ID_floatbv);

    exprt f_expr=
      static_cast<const exprt &>(type.find(ID_f));

    const source_locationt fraction_source_location =
      f_expr.find_source_location();

    typecheck_expr(f_expr);

    make_constant_index(f_expr);

    mp_integer f_int;
    if(to_integer(to_constant_expr(f_expr), f_int))
    {
      error().source_location = fraction_source_location;
      error() << "failed to convert number of fraction bits to constant" << eom;
      throw 0;
    }

    if(f_int<1 || f_int+1>=size_int)
    {
      error().source_location = fraction_source_location;
      error() << "floatbv fraction width invalid" << eom;
      throw 0;
    }

    type.remove(ID_f);
    type.set(ID_f, integer2string(f_int));
  }
  else
    UNREACHABLE;
}

void c_typecheck_baset::typecheck_code_type(code_typet &type)
{
  // the return type is still 'subtype()'
  type.return_type()=type.subtype();
  type.remove_subtype();

  code_typet::parameterst &parameters=type.parameters();

  // if we don't have any parameters, we assume it's (...)
  if(parameters.empty())
  {
    type.make_ellipsis();
  }
  else // we do have parameters
  {
    // is the last one ellipsis?
    if(type.parameters().back().id()==ID_ellipsis)
    {
      type.make_ellipsis();
      type.parameters().pop_back();
    }

    parameter_map.clear();

    for(auto &param : type.parameters())
    {
      // turn the declarations into parameters
      if(param.id()==ID_declaration)
      {
        ansi_c_declarationt &declaration=
          to_ansi_c_declaration(param);


        // first fix type
        code_typet::parametert parameter(
          declaration.full_type(declaration.declarator()));
        typet &param_type = parameter.type();
        std::list<codet> tmp_clean_code;
        tmp_clean_code.swap(clean_code); // ignore side-effects
        typecheck_type(param_type);
        tmp_clean_code.swap(clean_code);
        adjust_function_parameter(param_type);

        // adjust the identifier
        irep_idt identifier=declaration.declarator().get_name();

        // abstract or not?
        if(identifier.empty())
        {
          // abstract
          parameter.add_source_location()=declaration.type().source_location();
        }
        else
        {
          // make visible now, later parameters might use it
          parameter_map[identifier] = param_type;
          parameter.set_base_name(declaration.declarator().get_base_name());
          parameter.add_source_location()=
            declaration.declarator().source_location();
        }

        // put the parameter in place of the declaration
        param.swap(parameter);
      }
    }

    parameter_map.clear();

    if(parameters.size() == 1 && parameters[0].type().id() == ID_empty)
    {
      // if we just have one parameter of type void, remove it
      parameters.clear();
    }
  }

  typecheck_type(type.return_type());

  // 6.7.6.3:
  // "A function declarator shall not specify a return type that
  // is a function type or an array type."

  const typet &decl_return_type = type.return_type();

  if(decl_return_type.id() == ID_array)
  {
    error().source_location=type.source_location();
    error() << "function must not return array" << eom;
    throw 0;
  }

  if(decl_return_type.id() == ID_code)
  {
    error().source_location=type.source_location();
    error() << "function must not return function type" << eom;
    throw 0;
  }
}

void c_typecheck_baset::typecheck_array_type(array_typet &type)
{
  exprt &size=type.size();
  const source_locationt size_source_location = size.find_source_location();

  // check subtype
  typecheck_type(type.subtype());

  // we don't allow void as subtype
  if(type.subtype().id() == ID_empty)
  {
    error().source_location=type.source_location();
    error() << "array of voids" << eom;
    throw 0;
  }

  // we don't allow incomplete structs or unions as subtype
  const typet &followed_subtype = follow(type.subtype());

  if(
    (followed_subtype.id() == ID_struct || followed_subtype.id() == ID_union) &&
    to_struct_union_type(followed_subtype).is_incomplete())
  {
    // ISO/IEC 9899 6.7.5.2
    error().source_location = type.source_location();
    error() << "array has incomplete element type" << eom;
    throw 0;
  }

  // we don't allow functions as subtype
  if(type.subtype().id() == ID_code)
  {
    // ISO/IEC 9899 6.7.5.2
    error().source_location = type.source_location();
    error() << "array of function element type" << eom;
    throw 0;
  }

  // check size, if any

  if(size.is_not_nil())
  {
    typecheck_expr(size);
    make_index_type(size);

    // The size need not be a constant!
    // We simplify it, for the benefit of array initialisation.

    exprt tmp_size=size;
    add_rounding_mode(tmp_size);
    simplify(tmp_size, *this);

    if(tmp_size.is_constant())
    {
      mp_integer s;
      if(to_integer(to_constant_expr(tmp_size), s))
      {
        error().source_location = size_source_location;
        error() << "failed to convert constant: "
                << tmp_size.pretty() << eom;
        throw 0;
      }

      if(s<0)
      {
        error().source_location = size_source_location;
        error() << "array size must not be negative, "
                   "but got " << s << eom;
        throw 0;
      }

      size=tmp_size;
    }
    else if(tmp_size.id()==ID_infinity)
    {
      size=tmp_size;
    }
    else if(tmp_size.id()==ID_symbol &&
            tmp_size.type().get_bool(ID_C_constant))
    {
      // We allow a constant variable as array size, assuming
      // it won't change.
      // This criterion can be tricked:
      // Of course we can modify a 'const' symbol, e.g.,
      // using a pointer type cast. Interestingly,
      // at least gcc 4.2.1 makes the very same mistake!
      size=tmp_size;
    }
    else
    {
      // not a constant and not infinity

      PRECONDITION(!current_symbol.name.empty());

      if(current_symbol.is_static_lifetime)
      {
        error().source_location=current_symbol.location;
        error() << "array size of static symbol '" << current_symbol.base_name
                << "' is not constant" << eom;
        throw 0;
      }

      symbolt &new_symbol = get_fresh_aux_symbol(
        size_type(),
        id2string(current_symbol.name) + "$array_size",
        id2string(current_symbol.base_name) + "$array_size",
        size_source_location,
        mode,
        symbol_table);
      new_symbol.type.set(ID_C_constant, true);
      new_symbol.value = typecast_exprt::conditional_cast(size, size_type());

      // produce the code that declares and initializes the symbol
      symbol_exprt symbol_expr = new_symbol.symbol_expr();

      code_frontend_declt declaration(symbol_expr);
      declaration.add_source_location() = size_source_location;

      code_frontend_assignt assignment;
      assignment.lhs()=symbol_expr;
      assignment.rhs() = new_symbol.value;
      assignment.add_source_location() = size_source_location;

      // store the code
      clean_code.push_back(declaration);
      clean_code.push_back(assignment);

      // fix type
      size=symbol_expr;
    }
  }
}

void c_typecheck_baset::typecheck_vector_type(typet &type)
{
  // This turns the type with ID_frontend_vector into the type
  // with ID_vector; the difference is that the latter has
  // a constant as size, which we establish now.
  exprt size = static_cast<const exprt &>(type.find(ID_size));
  const source_locationt source_location = size.find_source_location();

  typecheck_expr(size);

  typet subtype = type.subtype();
  typecheck_type(subtype);

  // we are willing to combine 'vector' with various
  // other types, but not everything!

  if(subtype.id()!=ID_signedbv &&
     subtype.id()!=ID_unsignedbv &&
     subtype.id()!=ID_floatbv &&
     subtype.id()!=ID_fixedbv)
  {
    error().source_location=source_location;
    error() << "cannot make a vector of subtype "
            << to_string(subtype) << eom;
    throw 0;
  }

  make_constant_index(size);

  mp_integer s;
  if(to_integer(to_constant_expr(size), s))
  {
    error().source_location=source_location;
    error() << "failed to convert constant: "
            << size.pretty() << eom;
    throw 0;
  }

  if(s<=0)
  {
    error().source_location=source_location;
    error() << "vector size must be positive, "
               "but got " << s << eom;
    throw 0;
  }

  // the subtype must have constant size
  auto sub_size_expr_opt = size_of_expr(subtype, *this);

  if(!sub_size_expr_opt.has_value())
  {
    error().source_location = source_location;
    error() << "failed to determine size of vector base type '"
            << to_string(subtype) << "'" << eom;
    throw 0;
  }

  simplify(sub_size_expr_opt.value(), *this);

  const auto sub_size = numeric_cast<mp_integer>(sub_size_expr_opt.value());

  if(!sub_size.has_value())
  {
    error().source_location=source_location;
    error() << "failed to determine size of vector base type '"
            << to_string(subtype) << "'" << eom;
    throw 0;
  }

  if(*sub_size == 0)
  {
    error().source_location=source_location;
    error() << "type had size 0: '" << to_string(subtype) << "'" << eom;
    throw 0;
  }

  // adjust by width of base type
  if(s % *sub_size != 0)
  {
    error().source_location=source_location;
    error() << "vector size (" << s
            << ") expected to be multiple of base type size (" << *sub_size
            << ")" << eom;
    throw 0;
  }

  s /= *sub_size;

  // produce the type with ID_vector
  vector_typet new_type(subtype, from_integer(s, signed_size_type()));
  new_type.add_source_location() = source_location;
  new_type.size().add_source_location() = source_location;
  type = new_type;
}

void c_typecheck_baset::typecheck_compound_type(struct_union_typet &type)
{
  // These get replaced by symbol types later.
  irep_idt identifier;

  bool have_body=type.find(ID_components).is_not_nil();

  c_qualifierst original_qualifiers(type);

  // the type symbol, which may get re-used in other declarations, must not
  // carry any qualifiers (other than transparent_union, which isn't really a
  // qualifier)
  c_qualifierst remove_qualifiers;
  remove_qualifiers.is_transparent_union =
    original_qualifiers.is_transparent_union;
  remove_qualifiers.write(type);

  bool is_packed = type.get_bool(ID_C_packed);
  irept alignment = type.find(ID_C_alignment);

  if(type.find(ID_tag).is_nil())
  {
    // Anonymous? Must come with body.
    assert(have_body);

    // produce symbol
    symbolt compound_symbol;
    compound_symbol.is_type=true;
    compound_symbol.type=type;
    compound_symbol.location=type.source_location();

    typecheck_compound_body(to_struct_union_type(compound_symbol.type));

    std::string typestr = type2name(compound_symbol.type, *this);
    compound_symbol.base_name = "#anon#" + typestr;
    compound_symbol.name="tag-#anon#"+typestr;
    identifier=compound_symbol.name;

    // We might already have the same anonymous union/struct,
    // and this is simply ok. Note that the C standard treats
    // these as different types.
    if(symbol_table.symbols.find(identifier)==symbol_table.symbols.end())
    {
      symbolt *new_symbol;
      move_symbol(compound_symbol, new_symbol);
    }
  }
  else
  {
    identifier=type.find(ID_tag).get(ID_identifier);

    // does it exist already?
    symbol_tablet::symbolst::const_iterator s_it=
      symbol_table.symbols.find(identifier);

    if(s_it==symbol_table.symbols.end())
    {
      // no, add new symbol
      irep_idt base_name=type.find(ID_tag).get(ID_C_base_name);
      type.remove(ID_tag);
      type.set(ID_tag, base_name);

      symbolt compound_symbol;
      compound_symbol.is_type=true;
      compound_symbol.name=identifier;
      compound_symbol.base_name=base_name;
      compound_symbol.type=type;
      compound_symbol.location=type.source_location();
      compound_symbol.pretty_name=id2string(type.id())+" "+id2string(base_name);

      typet new_type=compound_symbol.type;

      // mark as incomplete
      to_struct_union_type(compound_symbol.type).make_incomplete();

      symbolt *new_symbol;
      move_symbol(compound_symbol, new_symbol);

      if(have_body)
      {
        typecheck_compound_body(to_struct_union_type(new_type));

        new_symbol->type.swap(new_type);
      }
    }
    else
    {
      // yes, it exists already
      if(
        s_it->second.type.id() == type.id() &&
        to_struct_union_type(s_it->second.type).is_incomplete())
      {
        // Maybe we got a body now.
        if(have_body)
        {
          irep_idt base_name=type.find(ID_tag).get(ID_C_base_name);
          type.remove(ID_tag);
          type.set(ID_tag, base_name);

          typecheck_compound_body(type);
          symbol_table.get_writeable_ref(s_it->first).type.swap(type);
        }
      }
      else if(s_it->second.type.id() != type.id())
      {
        error().source_location = type.source_location();
        error() << "redefinition of '" << s_it->second.pretty_name << "'"
                << " as different kind of tag" << eom;
        throw 0;
      }
      else if(have_body)
      {
        error().source_location=type.source_location();
        error() << "redefinition of body of '" << s_it->second.pretty_name
                << "'" << eom;
        throw 0;
      }
    }
  }

  typet tag_type;

  if(type.id() == ID_union)
    tag_type = union_tag_typet(identifier);
  else if(type.id() == ID_struct)
    tag_type = struct_tag_typet(identifier);
  else
    UNREACHABLE;

  tag_type.add_source_location() = type.source_location();
  type.swap(tag_type);

  original_qualifiers.write(type);

  if(is_packed)
    type.set(ID_C_packed, true);
  if(alignment.is_not_nil())
    type.set(ID_C_alignment, alignment);
}

void c_typecheck_baset::typecheck_compound_body(
  struct_union_typet &type)
{
  struct_union_typet::componentst &components=type.components();

  struct_union_typet::componentst old_components;
  old_components.swap(components);

  // We get these as declarations!
  for(auto &decl : old_components)
  {
    // the arguments are member declarations or static assertions
    assert(decl.id()==ID_declaration);

    ansi_c_declarationt &declaration=
      to_ansi_c_declaration(static_cast<exprt &>(decl));

    if(declaration.get_is_static_assert())
    {
      struct_union_typet::componentt new_component;
      new_component.id(ID_static_assert);
      new_component.add_source_location()=declaration.source_location();
      new_component.operands().swap(declaration.operands());
      assert(new_component.operands().size()==2);
      components.push_back(new_component);
    }
    else
    {
      // do first half of type
      typecheck_type(declaration.type());
      already_typechecked_typet::make_already_typechecked(declaration.type());

      for(const auto &declarator : declaration.declarators())
      {
        struct_union_typet::componentt new_component(
          declarator.get_base_name(), declaration.full_type(declarator));

        // There may be a declarator, which we use as location for
        // the component. Otherwise, use location of the declaration.
        const source_locationt source_location =
          declarator.get_name().empty() ? declaration.source_location()
                                        : declarator.source_location();

        new_component.add_source_location() = source_location;
        new_component.set_pretty_name(declarator.get_base_name());

        typecheck_type(new_component.type());

        if(!is_complete_type(new_component.type()) &&
           (new_component.type().id()!=ID_array ||
            !to_array_type(new_component.type()).is_incomplete()))
        {
          error().source_location = source_location;
          error() << "incomplete type not permitted here" << eom;
          throw 0;
        }

        if(new_component.type().id() == ID_empty)
        {
          error().source_location = source_location;
          error() << "void-typed member not permitted" << eom;
          throw 0;
        }

        components.push_back(new_component);
      }
    }
  }

  unsigned anon_member_counter=0;

  // scan for anonymous members, and name them
  for(auto &member : components)
  {
    if(!member.get_name().empty())
      continue;

    member.set_name("$anon"+std::to_string(anon_member_counter++));
    member.set_anonymous(true);
  }

  // scan for duplicate members

  {
    std::unordered_set<irep_idt> members;

    for(const auto &c : components)
    {
      if(!members.insert(c.get_name()).second)
      {
        error().source_location = c.source_location();
        error() << "duplicate member '" << c.get_name() << '\'' << eom;
        throw 0;
      }
    }
  }

  // We allow an incomplete (C99) array as _last_ member!
  // Zero-length is allowed everywhere.

  if(type.id()==ID_struct ||
     type.id()==ID_union)
  {
    for(struct_union_typet::componentst::iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      typet &c_type=it->type();

      if(c_type.id()==ID_array &&
         to_array_type(c_type).is_incomplete())
      {
        // needs to be last member
        if(type.id()==ID_struct && it!=--components.end())
        {
          error().source_location=it->source_location();
          error() << "flexible struct member must be last member" << eom;
          throw 0;
        }

        // make it zero-length
        c_type.id(ID_array);
        c_type.set(ID_size, from_integer(0, c_index_type()));
      }
    }
  }

  // We may add some minimal padding inside and at
  // the end of structs and
  // as additional member for unions.

  if(type.id()==ID_struct)
    add_padding(to_struct_type(type), *this);
  else if(type.id()==ID_union)
    add_padding(to_union_type(type), *this);

  // Now remove zero-width bit-fields, these are just
  // for adjusting alignment.
  for(struct_typet::componentst::iterator
      it=components.begin();
      it!=components.end();
      ) // blank
  {
    if(it->type().id()==ID_c_bit_field &&
       to_c_bit_field_type(it->type()).get_width()==0)
      it=components.erase(it);
    else
      it++;
  }

  // finally, check _Static_assert inside the compound
  for(struct_union_typet::componentst::iterator
      it=components.begin();
      it!=components.end();
      ) // no it++
  {
    if(it->id()==ID_static_assert)
    {
      if(config.ansi_c.mode == configt::ansi_ct::flavourt::VISUAL_STUDIO)
      {
        error().source_location = it->source_location();
        error() << "static_assert not supported in compound body" << eom;
        throw 0;
      }

      exprt &assertion = to_binary_expr(*it).op0();
      typecheck_expr(assertion);
      typecheck_expr(to_binary_expr(*it).op1());
      assertion = typecast_exprt(assertion, bool_typet());
      make_constant(assertion);

      if(assertion.is_false())
      {
        error().source_location=it->source_location();
        error() << "failed _Static_assert" << eom;
        throw 0;
      }
      else if(!assertion.is_true())
      {
        // should warn/complain
      }

      it=components.erase(it);
    }
    else
      it++;
  }
}

typet c_typecheck_baset::enum_constant_type(
  const mp_integer &min_value,
  const mp_integer &max_value) const
{
  if(config.ansi_c.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO)
  {
    return signed_int_type();
  }
  else
  {
    // enum constants are at least 'int', but may be made larger.
    // 'Packing' has no influence.
    if(max_value<(mp_integer(1)<<(config.ansi_c.int_width-1)) &&
       min_value>=-(mp_integer(1)<<(config.ansi_c.int_width-1)))
      return signed_int_type();
    else if(max_value<(mp_integer(1)<<config.ansi_c.int_width) &&
            min_value>=0)
      return unsigned_int_type();
    else if(max_value<(mp_integer(1)<<config.ansi_c.long_int_width) &&
            min_value>=0)
      return unsigned_long_int_type();
    else if(max_value<(mp_integer(1)<<config.ansi_c.long_long_int_width) &&
            min_value>=0)
      return unsigned_long_long_int_type();
    else if(max_value<(mp_integer(1)<<(config.ansi_c.long_int_width-1)) &&
            min_value>=-(mp_integer(1)<<(config.ansi_c.long_int_width-1)))
      return signed_long_int_type();
    else
      return signed_long_long_int_type();
  }
}

bitvector_typet c_typecheck_baset::enum_underlying_type(
  const mp_integer &min_value,
  const mp_integer &max_value,
  bool is_packed) const
{
  if(config.ansi_c.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO)
  {
    return signed_int_type();
  }
  else
  {
    if(min_value<0)
    {
      // We'll want a signed type.

      if(is_packed)
      {
        // If packed, there are smaller options.
        if(max_value<(mp_integer(1)<<(config.ansi_c.char_width-1)) &&
           min_value>=-(mp_integer(1)<<(config.ansi_c.char_width-1)))
          return signed_char_type();
        else if(max_value<(mp_integer(1)<<(config.ansi_c.short_int_width-1)) &&
                min_value>=-(mp_integer(1)<<(config.ansi_c.short_int_width-1)))
          return signed_short_int_type();
      }

      if(max_value<(mp_integer(1)<<(config.ansi_c.int_width-1)) &&
         min_value>=-(mp_integer(1)<<(config.ansi_c.int_width-1)))
        return signed_int_type();
      else if(max_value<(mp_integer(1)<<(config.ansi_c.long_int_width-1)) &&
              min_value>=-(mp_integer(1)<<(config.ansi_c.long_int_width-1)))
        return signed_long_int_type();
      else
        return signed_long_long_int_type();
    }
    else
    {
      // We'll want an unsigned type.

      if(is_packed)
      {
        // If packed, there are smaller options.
        if(max_value<(mp_integer(1)<<config.ansi_c.char_width))
          return unsigned_char_type();
        else if(max_value<(mp_integer(1)<<config.ansi_c.short_int_width))
          return unsigned_short_int_type();
      }

      if(max_value<(mp_integer(1)<<config.ansi_c.int_width))
        return unsigned_int_type();
      else if(max_value<(mp_integer(1)<<config.ansi_c.long_int_width))
        return unsigned_long_int_type();
      else
        return unsigned_long_long_int_type();
    }
  }
}

void c_typecheck_baset::typecheck_c_enum_type(typet &type)
{
  // These come with the declarations
  // of the enum constants as operands.

  exprt &as_expr=static_cast<exprt &>(static_cast<irept &>(type));
  source_locationt source_location=type.source_location();

  // We allow empty enums in the grammar to get better
  // error messages.
  if(as_expr.operands().empty())
  {
    error().source_location=source_location;
    error() << "empty enum" << eom;
    throw 0;
  }

  const bool have_underlying_type =
    type.find_type(ID_enum_underlying_type).is_not_nil();

  if(have_underlying_type)
  {
    typecheck_type(type.add_type(ID_enum_underlying_type));

    const typet &underlying_type =
      static_cast<const typet &>(type.find(ID_enum_underlying_type));

    if(!is_signed_or_unsigned_bitvector(underlying_type))
    {
      std::ostringstream msg;
      msg << source_location << ": non-integral type '"
          << underlying_type.get(ID_C_c_type)
          << "' is an invalid underlying type";
      throw invalid_source_file_exceptiont{msg.str()};
    }
  }

  // enums start at zero;
  // we also track min and max to find a nice base type
  mp_integer value=0, min_value=0, max_value=0;

  std::list<c_enum_typet::c_enum_membert> enum_members;

  // We need to determine a width, and a signedness
  // to obtain an 'underlying type'.
  // We just do int, but gcc might pick smaller widths
  // if the type is marked as 'packed'.
  // gcc/clang may also pick a larger width. Visual Studio doesn't.

  for(auto &op : as_expr.operands())
  {
    ansi_c_declarationt &declaration=to_ansi_c_declaration(op);
    exprt &v=declaration.declarator().value();

    if(v.is_not_nil()) // value given?
    {
      exprt tmp_v=v;
      typecheck_expr(tmp_v);
      add_rounding_mode(tmp_v);
      simplify(tmp_v, *this);
      if(tmp_v.is_true())
        value=1;
      else if(tmp_v.is_false())
        value=0;
      else if(
        tmp_v.id() == ID_constant &&
        !to_integer(to_constant_expr(tmp_v), value))
      {
      }
      else
      {
        error().source_location=v.source_location();
        error() << "enum is not a constant" << eom;
        throw 0;
      }
    }

    if(value<min_value)
      min_value=value;
    if(value>max_value)
      max_value=value;

    typet constant_type;

    if(have_underlying_type)
    {
      constant_type = type.find_type(ID_enum_underlying_type);
      const auto &tmp = to_integer_bitvector_type(constant_type);

      if(value < tmp.smallest() || value > tmp.largest())
      {
        std::ostringstream msg;
        msg
          << v.source_location()
          << ": enumerator value is not representable in the underlying type '"
          << constant_type.get(ID_C_c_type) << "'";
        throw invalid_source_file_exceptiont{msg.str()};
      }
    }
    else
    {
      constant_type = enum_constant_type(min_value, max_value);
    }

    v=from_integer(value, constant_type);

    declaration.type()=constant_type;
    typecheck_declaration(declaration);

    irep_idt base_name=
      declaration.declarator().get_base_name();

    irep_idt identifier=
      declaration.declarator().get_name();

    // store
    c_enum_typet::c_enum_membert member;
    member.set_identifier(identifier);
    member.set_base_name(base_name);
    // Note: The value will be correctly set to a bv type when we know
    // the width of the bitvector
    member.set_value(integer2string(value));
    enum_members.push_back(member);

    // produce value for next constant
    ++value;
  }

  // Remove these now; we add them to the
  // c_enum symbol later.
  as_expr.operands().clear();

  bool is_packed=type.get_bool(ID_C_packed);

  // We use a subtype to store the underlying type.
  bitvector_typet underlying_type(ID_nil);

  if(have_underlying_type)
  {
    underlying_type =
      to_bitvector_type(type.find_type(ID_enum_underlying_type));
  }
  else
  {
    underlying_type = enum_underlying_type(min_value, max_value, is_packed);
  }

  // Get the width to make the values have a bitvector type
  std::size_t width = underlying_type.get_width();
  for(auto &member : enum_members)
  {
    // Note: This is inefficient as it first turns integers to strings
    // and then turns them back to bvrep
    auto value = string2integer(id2string(member.get_value()));
    member.set_value(integer2bvrep(value, width));
  }

  // tag?
  if(type.find(ID_tag).is_nil())
  {
    // None, it's anonymous. We generate a tag.
    std::string anon_identifier="#anon_enum";

    for(const auto &member : enum_members)
    {
      anon_identifier+='$';
      anon_identifier+=id2string(member.get_base_name());
      anon_identifier+='=';
      anon_identifier+=id2string(member.get_value());
    }

    if(is_packed)
      anon_identifier+="#packed";

    type.add(ID_tag).set(ID_identifier, anon_identifier);
  }

  irept &tag=type.add(ID_tag);
  irep_idt base_name=tag.get(ID_C_base_name);
  irep_idt identifier=tag.get(ID_identifier);

  // Put into symbol table
  symbolt enum_tag_symbol;

  enum_tag_symbol.is_type=true;
  enum_tag_symbol.type=type;
  enum_tag_symbol.location=source_location;
  enum_tag_symbol.is_file_local=true;
  enum_tag_symbol.base_name=base_name;
  enum_tag_symbol.name=identifier;

  // throw in the enum members as 'body'
  irept::subt &body=enum_tag_symbol.type.add(ID_body).get_sub();

  for(const auto &member : enum_members)
    body.push_back(member);

  enum_tag_symbol.type.subtype()=underlying_type;

  // is it in the symbol table already?
  symbol_tablet::symbolst::const_iterator s_it=
    symbol_table.symbols.find(identifier);

  if(s_it!=symbol_table.symbols.end())
  {
    // Yes.
    const symbolt &symbol=s_it->second;

    if(symbol.type.id() != ID_c_enum)
    {
      error().source_location = source_location;
      error() << "use of tag that does not match previous declaration" << eom;
      throw 0;
    }

    if(to_c_enum_type(symbol.type).is_incomplete())
    {
      // Ok, overwrite the type in the symbol table.
      // This gives us the members and the subtype.
      symbol_table.get_writeable_ref(symbol.name).type=enum_tag_symbol.type;
    }
    else
    {
      // We might already have the same anonymous enum, and this is
      // simply ok. Note that the C standard treats these as
      // different types.
      if(!base_name.empty())
      {
        error().source_location=type.source_location();
        error() << "redeclaration of enum tag" << eom;
        throw 0;
      }
    }
  }
  else
  {
    symbolt *new_symbol;
    move_symbol(enum_tag_symbol, new_symbol);
  }

  // We produce a c_enum_tag as the resulting type.
  type.id(ID_c_enum_tag);
  type.remove(ID_tag);
  type.set(ID_identifier, identifier);
}

void c_typecheck_baset::typecheck_c_enum_tag_type(c_enum_tag_typet &type)
{
  // It's just a tag.

  if(type.find(ID_tag).is_nil())
  {
    error().source_location=type.source_location();
    error() << "anonymous enum tag without members" << eom;
    throw 0;
  }

  if(type.find(ID_enum_underlying_type).is_not_nil())
  {
    warning().source_location = type.source_location();
    warning() << "ignoring specification of underlying type for enum" << eom;
  }

  source_locationt source_location=type.source_location();

  irept &tag=type.add(ID_tag);
  irep_idt base_name=tag.get(ID_C_base_name);
  irep_idt identifier=tag.get(ID_identifier);

  // is it in the symbol table?
  symbol_tablet::symbolst::const_iterator s_it=
    symbol_table.symbols.find(identifier);

  if(s_it!=symbol_table.symbols.end())
  {
    // Yes.
    const symbolt &symbol=s_it->second;

    if(symbol.type.id() != ID_c_enum)
    {
      error().source_location=source_location;
      error() << "use of tag that does not match previous declaration" << eom;
      throw 0;
    }
  }
  else
  {
    // no, add it as an incomplete c_enum
    c_enum_typet new_type(signed_int_type()); // default subtype
    new_type.add(ID_tag)=tag;
    new_type.make_incomplete();

    symbolt enum_tag_symbol;

    enum_tag_symbol.is_type=true;
    enum_tag_symbol.type=new_type;
    enum_tag_symbol.location=source_location;
    enum_tag_symbol.is_file_local=true;
    enum_tag_symbol.base_name=base_name;
    enum_tag_symbol.name=identifier;

    symbolt *new_symbol;
    move_symbol(enum_tag_symbol, new_symbol);
  }

  // Clean up resulting type
  type.remove(ID_tag);
  type.set_identifier(identifier);
}

void c_typecheck_baset::typecheck_c_bit_field_type(c_bit_field_typet &type)
{
  typecheck_type(type.subtype());

  mp_integer i;

  {
    exprt &width_expr=static_cast<exprt &>(type.add(ID_size));

    typecheck_expr(width_expr);
    make_constant_index(width_expr);

    if(to_integer(to_constant_expr(width_expr), i))
    {
      error().source_location=type.source_location();
      error() << "failed to convert bit field width" << eom;
      throw 0;
    }

    if(i<0)
    {
      error().source_location=type.source_location();
      error() << "bit field width is negative" << eom;
      throw 0;
    }

    type.set_width(numeric_cast_v<std::size_t>(i));
    type.remove(ID_size);
  }

  const typet &subtype = type.subtype();

  std::size_t sub_width=0;

  if(subtype.id()==ID_bool)
  {
    // This is the 'proper' bool.
    sub_width=1;
  }
  else if(subtype.id()==ID_signedbv ||
          subtype.id()==ID_unsignedbv ||
          subtype.id()==ID_c_bool)
  {
    sub_width=to_bitvector_type(subtype).get_width();
  }
  else if(subtype.id()==ID_c_enum_tag)
  {
    // These point to an enum, which has a sub-subtype,
    // which may be smaller or larger than int, and we thus have
    // to check.
    const auto &c_enum_type =
      to_c_enum_type(follow_tag(to_c_enum_tag_type(subtype)));

    if(c_enum_type.is_incomplete())
    {
      error().source_location=type.source_location();
      error() << "bit field has incomplete enum type" << eom;
      throw 0;
    }

    sub_width = to_bitvector_type(c_enum_type.subtype()).get_width();
  }
  else
  {
    error().source_location=type.source_location();
    error() << "bit field with non-integer type: "
            << to_string(subtype) << eom;
    throw 0;
  }

  if(i>sub_width)
  {
    error().source_location=type.source_location();
    error() << "bit field (" << i
            << " bits) larger than type (" << sub_width << " bits)"
            << eom;
    throw 0;
  }
}

void c_typecheck_baset::typecheck_typeof_type(typet &type)
{
  // save location
  source_locationt source_location=type.source_location();

  // retain the qualifiers as is
  c_qualifierst c_qualifiers;
  c_qualifiers.read(type);

  const auto &as_expr = (const exprt &)type;

  if(!as_expr.has_operands())
  {
    typet t=static_cast<const typet &>(type.find(ID_type_arg));
    typecheck_type(t);
    type.swap(t);
  }
  else
  {
    exprt expr = to_unary_expr(as_expr).op();
    typecheck_expr(expr);

    // undo an implicit address-of
    if(expr.id()==ID_address_of &&
       expr.get_bool(ID_C_implicit))
    {
      expr = to_address_of_expr(expr).object();
    }

    type.swap(expr.type());
  }

  type.add_source_location()=source_location;
  c_qualifiers.write(type);
}

void c_typecheck_baset::typecheck_typedef_type(typet &type)
{
  const irep_idt &identifier = to_typedef_type(type).get_identifier();

  symbol_tablet::symbolst::const_iterator s_it =
    symbol_table.symbols.find(identifier);

  if(s_it == symbol_table.symbols.end())
  {
    error().source_location = type.source_location();
    error() << "typedef symbol '" << identifier << "' not found" << eom;
    throw 0;
  }

  const symbolt &symbol = s_it->second;

  if(!symbol.is_type)
  {
    error().source_location = type.source_location();
    error() << "expected type symbol for typedef" << eom;
    throw 0;
  }

  // overwrite, but preserve (add) any qualifiers and other flags

  c_qualifierst c_qualifiers(type);
  bool is_packed = type.get_bool(ID_C_packed);
  irept alignment = type.find(ID_C_alignment);

  c_qualifiers += c_qualifierst(symbol.type);
  type = symbol.type;
  c_qualifiers.write(type);

  if(is_packed)
    type.set(ID_C_packed, true);
  if(alignment.is_not_nil())
    type.set(ID_C_alignment, alignment);

  // CPROVER extensions
  if(symbol.base_name == CPROVER_PREFIX "rational")
  {
    type=rational_typet();
  }
  else if(symbol.base_name == CPROVER_PREFIX "integer")
  {
    type=integer_typet();
  }
}

void c_typecheck_baset::adjust_function_parameter(typet &type) const
{
  if(type.id()==ID_array)
  {
    source_locationt source_location=type.source_location();
    type=pointer_type(type.subtype());
    type.add_source_location()=source_location;
  }
  else if(type.id()==ID_code)
  {
    // see ISO/IEC 9899:1999 page 199 clause 8,
    // may be hidden in typedef
    source_locationt source_location=type.source_location();
    type=pointer_type(type);
    type.add_source_location()=source_location;
  }
  else if(type.id()==ID_KnR)
  {
    // any KnR args without type yet?
    type=signed_int_type(); // the default is integer!
    // no source location
  }
}
