/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <config.h>
#include <simplify_expr.h>
#include <arith_tools.h>
#include <std_types.h>
#include <i2string.h>
#include <expr_util.h>
#include <pointer_offset_size.h>

#include "c_typecheck_base.h"
#include "c_types.h"
#include "c_sizeof.h"
#include "c_qualifiers.h"

/*******************************************************************\

Function: c_typecheck_baset::typecheck_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_type(typet &type)
{
  if(type.id()==ID_code)
    typecheck_code_type(to_code_type(type));
  else if(type.id()==ID_array)
    typecheck_array_type(to_array_type(type));
  else if(type.id()==ID_incomplete_array)
    typecheck_type(type.subtype());
  else if(type.id()==ID_pointer)
    typecheck_type(type.subtype());
  else if(type.id()==ID_struct ||
          type.id()==ID_union)
    typecheck_compound_type(to_struct_union_type(type));
  else if(type.id()==ID_c_enum)
  {
  }
  else if(type.id()==ID_c_bitfield)
    typecheck_c_bit_field_type(type);
  else if(type.id()==ID_typeof)
    typecheck_typeof_type(type);
  else if(type.id()==ID_symbol)
    typecheck_symbol_type(type);
  else if(type.id()==ID_vector)
    typecheck_vector_type(to_vector_type(type));
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_code_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_code_type(code_typet &type)
{
  code_typet::argumentst &arguments=type.arguments();

  // if we don't have any arguments, we assume it's (...)
  if(arguments.empty())
  {
    type.make_ellipsis();
  }
  else if(arguments.size()==1 &&
          arguments[0].type().id()==ID_empty)
  {
    // if we just have one argument of type void, remove it
    arguments.clear();
  }
  else
  {
    for(unsigned i=0; i<type.arguments().size(); i++)
    {
      code_typet::argumentt &argument=type.arguments()[i];

      // first fix type
      typet &type=argument.type();

      typecheck_type(type);
      adjust_function_argument(type);
    }
  }

  typecheck_type(type.return_type());
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_array_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_array_type(array_typet &type)
{
  exprt &size=type.size();
  locationt location=size.find_location();

  // check subtype
  typecheck_type(type.subtype());

  // check size  
  typecheck_expr(size);
  make_index_type(size);
  
  // the size need not be a constant!
  // we simplify it, for the benefit of array initialisation
  simplify(size, *this);

  if(size.is_constant())
  {
    mp_integer s;
    if(to_integer(size, s))
    {
      err_location(location);
      str << "failed to convert constant: "
          << size.pretty();
      throw 0;
    }

    if(s<0)
    {
      err_location(location);
      str << "array size must not be negative, "
             "but got " << s;
      throw 0;
    }
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_vector_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_vector_type(vector_typet &type)
{
  exprt &size=type.size();
  locationt size_location=size.find_location();

  typecheck_expr(size);
  
  typet &subtype=type.subtype();
  typecheck_type(subtype);

  // we are willing to combine 'vector' with various
  // other types, but not everything!

  if(subtype.id()!=ID_signedbv &&
     subtype.id()!=ID_unsignedbv &&
     subtype.id()!=ID_floatbv &&
     subtype.id()!=ID_fixedbv)
  {
    err_location(size_location);
    error("cannot make a vector of this type");
    throw 0;
  }

  make_constant_index(size);

  mp_integer s;
  if(to_integer(size, s))
  {
    err_location(size_location);
    str << "failed to convert constant: "
        << size.pretty();
    throw 0;
  }

  if(s<=0)
  {
    err_location(size_location);
    str << "vector size must be positive, "
           "but got " << s;
    throw 0;
  }
  
  exprt size_expr=c_sizeof(type.subtype(), *this);
  
  simplify(size_expr, *this);

  mp_integer sub_size;
  
  if(to_integer(size_expr, sub_size))
  {
    err_location(size_location);
    str << "failed to determine size of vector base type `"
        << to_string(type.subtype()) << "'";
    throw 0;
  }
  
  // adjust by width of base type
  if(s%sub_size!=0)
  {
    err_location(size_location);
    str << "vector size expected to be multiple of base type size";
    throw 0;
  }
  
  s/=sub_size;

  type.set(ID_size, from_integer(s, signed_size_type()));
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_compound_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_compound_type(struct_union_typet &type)
{
  struct_union_typet::componentst &components=type.components();
  
  // mark bit-fields
  for(struct_union_typet::componentst::iterator
      it=components.begin();
      it!=components.end();
      it++)
    if(it->type().id()==ID_c_bitfield)
      it->set_is_bit_field(true);

  // check subtypes
  for(struct_union_typet::componentst::iterator
      it=components.begin();
      it!=components.end();
      it++)
    typecheck_type(it->type());

  unsigned anon_member_counter=0;

  // scan for anonymous members, and name them
  for(struct_union_typet::componentst::iterator
      it=components.begin();
      it!=components.end();
      it++)
  {
    if(it->get_name()!=irep_idt()) continue;

    it->set_name("$anon"+i2string(anon_member_counter++));
    it->set_anonymous(true);
  }

  // scan for duplicate members

  {
    hash_set_cont<irep_idt, irep_id_hash> members;

    for(struct_union_typet::componentst::iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      if(!members.insert(it->get_name()).second)
      {
        // we do nothing (as gcc won't complain)
      }
    }
  }
  
  // we may add some minimal padding inside structs (not unions)
  // unless there is an attribute that says that the struct is
  // 'packed'

  if(type.id()==ID_struct &&
     !type.get_bool(ID_packed))
    add_padding(to_struct_type(type));

  // we allow a zero-length (GCC) or incomplete (C99) array
  // as _last_ member!

  for(struct_union_typet::componentst::iterator
      it=components.begin();
      it!=components.end();
      it++)
  {
    typet &type=it->type();
  
    if((type.id()==ID_array &&
        to_array_type(type).size().is_zero()) ||
       type.id()==ID_incomplete_array)
    {
      // needs to be last member
      if(it!=--components.end())
      {
        err_location(*it);
        throw "flexible struct member must be last member";
      }
      
      // if it's incomplete, make it zero
      if(type.id()==ID_incomplete_array)
      {
        type.id(ID_array);
        type.set(ID_size, gen_zero(index_type()));
      }
    }
  }  
}

/*******************************************************************\

Function: alignment_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static const typet &alignment_type(const typet &type)
{
  if(type.id()==ID_array)
    return alignment_type(type.subtype());
  else if(type.id()==ID_struct)
  {
    const struct_typet::componentst &components=
      to_struct_type(type).components();

    if(!components.empty())
      return alignment_type(components.front().type());
  }

  return type;
}

/*******************************************************************\

Function: c_typecheck_baset::alignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned c_typecheck_baset::alignment(const typet &type) const
{
  if(type.id()==ID_array ||
     type.id()==ID_incomplete_array)
    return alignment(type.subtype());
  else if(type.id()==ID_struct || type.id()==ID_union)
  {
    const struct_union_typet::componentst &components=
      to_struct_union_type(type).components();

    unsigned result=1;

    // get the max
    // (should really be the smallest common denominator)
    for(struct_union_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
      result=std::max(result, alignment(it->type()));

    return result;
  }
  else if(type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv ||
          type.id()==ID_fixedbv ||
          type.id()==ID_floatbv)
  {
    unsigned width=type.get_int(ID_width);
    return width%8?width/8+1:width/8;
  }
  else if(type.id()==ID_pointer)
  {
    unsigned width=config.ansi_c.pointer_width;
    return width%8?width/8+1:width/8;
  }
  else if(type.id()==ID_symbol)
    return alignment(follow(type));

  return 1;
}

/*******************************************************************\

Function: c_typecheck_baset::add_padding

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::add_padding(struct_typet &type)
{
  struct_typet::componentst &components=type.components();

  mp_integer offset=0;
  unsigned padding_counter=0;

  for(struct_typet::componentst::iterator
      it=components.begin();
      it!=components.end();
      it++)
  {
    // bit-fields do not get padded
    if(it->get_is_bit_field())
      continue;
  
    const typet &it_type=it->type();
    unsigned a=alignment(it_type);
    
    // check minimum alignment
    if(a<config.ansi_c.alignment)
      a=config.ansi_c.alignment;
      
    if(a!=1)
    {
      // we may need to align it
      unsigned displacement=integer2long(offset%a);

      if(displacement!=0)
      {
        unsigned pad=a-displacement;
      
        unsignedbv_typet padding_type;
        padding_type.set_width(pad*8);
        
        struct_typet::componentt component;
        component.type()=padding_type;
        component.set_name("$pad"+i2string(padding_counter++));
        component.set_is_padding(true);
        
        it=components.insert(it, component);
        it++; // skip over
        
        offset+=pad;
      }
    }
    
    mp_integer size=pointer_offset_size(*this, it_type);
    offset+=size;
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_c_bit_field_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_c_bit_field_type(typet &type)
{
  typecheck_type(type.subtype());

  exprt &width_expr=static_cast<exprt &>(type.add(ID_size));

  typecheck_expr(width_expr);
  make_constant_index(width_expr);

  mp_integer i;
  if(to_integer(width_expr, i))
  {
    err_location(type);
    throw "failed to convert bit field width";
  }

  if(i<0)
  {
    err_location(type);
    throw "bit field width is negative";
  }

  const typet &base_type=follow(type.subtype());
  
  if(base_type.id()==ID_bool)
  {
    if(i>1)
    {
      err_location(type);
      throw "bit field width too large";
    }

    // We don't use bool, as it's really a byte long.
    type.id(ID_unsignedbv);
    type.set(ID_width, integer2long(i));
  }
  else if(base_type.id()==ID_signedbv ||
          base_type.id()==ID_unsignedbv ||
          base_type.id()==ID_c_enum)
  {
    unsigned width=base_type.get_int(ID_width);

    if(i>width)
    {
      err_location(type);
      throw "bit field width too large";
    }

    typet tmp(base_type);
    type.swap(tmp);
    type.set(ID_width, integer2string(i));
  }
  else
  {
    err_location(type);
    str << "bit field with non-integer type: "
        << to_string(base_type);
    throw 0;
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_typeof_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_typeof_type(typet &type)
{
  // retain the qualifiers as is
  c_qualifierst c_qualifiers;
  c_qualifiers.read(type);

  if(type.find(ID_operands).is_nil())
  {
    typet t=static_cast<const typet &>(type.find(ID_type_arg));
    typecheck_type(t);
    type.swap(t);
  }
  else
  {
    exprt expr=((const exprt &)type).op0();
    typecheck_expr(expr);

    // undo an implicit address-of
    if(expr.id()==ID_address_of &&
       expr.get_bool(ID_C_implicit))
    {
      assert(expr.operands().size()==1);
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
    }

    type.swap(expr.type());
  }
  
  c_qualifiers.write(type);
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_symbol_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_symbol_type(typet &type)
{
  // adjust identifier, if needed
  replace_symbol(type);

  const irep_idt &identifier=type.get(ID_identifier);

  contextt::symbolst::const_iterator s_it=context.symbols.find(identifier);

  if(s_it==context.symbols.end())
  {
    err_location(type);
    str << "type symbol `" << identifier << "' not found";
    throw 0;
  }

  const symbolt &symbol=s_it->second;

  if(!symbol.is_type)
  {
    err_location(type);
    throw "expected type symbol";
  }
  
  if(symbol.is_macro)
  {
    c_qualifierst c_qualifiers;
    c_qualifiers.read(type);
    type=symbol.type; // overwrite
    c_qualifiers.write(type);
  }
    
  // an extension
  if(symbol.base_name=="__CPROVER_rational")
  {
    type=rational_typet();
  }
  else if(symbol.base_name=="__CPROVER_integer")
  {
    type=integer_typet();
  }
}

/*******************************************************************\

Function: c_typecheck_baset::adjust_function_argument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::adjust_function_argument(typet &type) const
{
  if(type.id()==ID_array ||
     type.id()==ID_incomplete_array)
  {
    type.id(ID_pointer);
    type.remove(ID_size);
    type.remove(ID_C_constant);
  }
  else if(type.id()==ID_code)
  {
    // see ISO/IEC 9899:1999 page 199 clause 8
    pointer_typet tmp;
    tmp.subtype()=type;
    type.swap(tmp);
  }
  else if(type.id()==ID_KnR)
  {
    // any KnR args without type yet?
    type=int_type(); // the default is integer!
  }
}

/*******************************************************************\

Function: c_typecheck_baset::clean_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::clean_type(
  const symbolt &base_symbol,
  typet &type)
{
  if(type.id()==ID_symbol)
  {
    // we need to follow for structs and such, but only once
    irep_idt identifier=to_symbol_type(type).get_identifier();
    if(already_cleaned.insert(identifier).second)
    {
      contextt::symbolst::iterator s_it=context.symbols.find(identifier);
      assert(s_it!=context.symbols.end());
      clean_type(base_symbol, s_it->second.type);
    }
  }
  else if(type.id()==ID_array)
  {
    array_typet &array_type=to_array_type(type);
  
    clean_type(base_symbol, array_type.subtype());

    // the size need not be a constant!
    // this was simplified already by typecheck_array_type
    
    exprt &size=array_type.size();
    
    if(!size.is_constant() &&
       size.id()!=ID_infinity)
    {
      // Need to pull out! We insert new symbol.
      unsigned count=0;
      irep_idt temp_identifier;
      std::string suffix;
      do
      {
        suffix="#array_size"+i2string(count);
        temp_identifier=id2string(base_symbol.name)+suffix;
        count++;
      }
      while(context.symbols.find(temp_identifier)!=context.symbols.end());

      // add the symbol to context
      symbolt new_symbol;
      new_symbol.name=temp_identifier;
      new_symbol.pretty_name=id2string(base_symbol.pretty_name)+suffix;
      new_symbol.base_name=id2string(base_symbol.base_name)+suffix;
      new_symbol.type=size.type();
      new_symbol.file_local=true;
      new_symbol.is_type=false;
      new_symbol.value.make_nil();
      context.add(new_symbol);

      // produce the code that initializes the symbol      
      symbol_exprt symbol_expr;
      symbol_expr.set_identifier(temp_identifier);
      symbol_expr.type()=size.type();
      code_assignt assignment;
      assignment.lhs()=symbol_expr;
      assignment.rhs()=size;
      assignment.location()=array_type.size().location();

      // store the code

      // fix type
      size=symbol_expr;
    }
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union)
  {
    struct_union_typet::componentst &components=
      to_struct_union_type(type).components();

    for(struct_union_typet::componentst::iterator
        it=components.begin();
        it!=components.end();
        it++)
      clean_type(base_symbol, it->type());
  }
  else if(type.id()==ID_code)
  {
    // done, can't contain arrays
  }
  else if(type.id()==ID_pointer)
  {
    clean_type(base_symbol, type.subtype());
  }
  else if(type.id()==ID_vector)
  {
    // should be clean
  }
}

