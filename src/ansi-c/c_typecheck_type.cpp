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
#include "padding.h"

/*******************************************************************\

Function: c_typecheck_baset::typecheck_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_type(typet &type)
{
  // we first convert, and then check
  
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
  else
  {
    for(unsigned i=0; i<type.arguments().size(); i++)
    {
      code_typet::argumentt &argument=type.arguments()[i];

      // first fix type
      typet &type=argument.type();

      typecheck_type(type);
      
      adjust_function_argument(type);
      
      // adjust the identifier

      irep_idt identifier=argument.get_identifier();

      if(identifier!=irep_idt())
      {
        identifier=add_language_prefix(identifier);
    
        id_replace_mapt::const_iterator
          m_it=id_replace_map.find(identifier);

        if(m_it!=id_replace_map.end())
          identifier=m_it->second;

        argument.set_identifier(identifier);
      }
    }
  
    if(arguments.size()==1 &&
       follow(arguments[0].type()).id()==ID_empty)
    {
      // if we just have one argument of type void, remove it
      arguments.clear();
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

  // check size, if any
  
  if(size.is_not_nil())
  {
    typecheck_expr(size);
    make_index_type(size);
    
    // The size need not be a constant!
    // We simplify it, for the benefit of array initialisation.
    
    exprt tmp_size=size;
    simplify(tmp_size, *this);

    if(tmp_size.is_constant())
    {
      mp_integer s;
      if(to_integer(tmp_size, s))
      {
        err_location(location);
        str << "failed to convert constant: "
            << tmp_size.pretty();
        throw 0;
      }

      if(s<0)
      {
        err_location(location);
        str << "array size must not be negative, "
               "but got " << s;
        throw 0;
      }
      
      size=tmp_size;
    }
    else if(tmp_size.id()==ID_infinity)
      size=tmp_size;
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
  
  // the subtype must have constant size
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
    {
      it->set_is_bit_field(true);
      typet tmp=it->type().subtype();
      typecheck_type(tmp);
      it->set_bit_field_type(tmp);
    }

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
  
  // We allow an incomplete (C99) array as _last_ member!
  // Zero-length is allowed everywhere.

  if(type.id()==ID_struct)
  {
    for(struct_union_typet::componentst::iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      typet &type=it->type();
    
      if(type.id()==ID_array &&
         to_array_type(type).is_incomplete())
      {
        // needs to be last member
        if(it!=--components.end())
        {
          err_location(*it);
          throw "flexible struct member must be last member";
        }
        
        // make it zero-length
        type.id(ID_array);
        type.set(ID_size, gen_zero(index_type()));
      }
    }  
  }

  // we may add some minimal padding inside structs (not unions)
  // unless there is an attribute that says that the struct is
  // 'packed'

  if(type.id()==ID_struct)
    add_padding(to_struct_type(type), *this);

  // finally, check _Static_assert inside the compound
  for(struct_union_typet::componentst::iterator
      it=components.begin();
      it!=components.end();
      ) // no it++
  {
    if(it->id()==ID_code && it->get(ID_statement)==ID_static_assert)
    {
      assert(it->operands().size()==2);
      exprt &assertion=it->op0();
      typecheck_expr(assertion);
      typecheck_expr(it->op1());
      assertion.make_typecast(bool_typet());
      make_constant(assertion);
      
      if(assertion.is_false())
      {
        err_location(*it);
        throw "failed _Static_assert";
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
  {
    // add prefix
    symbol_typet &symbol_type=to_symbol_type(type);
    symbol_type.set_identifier(add_language_prefix(symbol_type.get_identifier()));
  }

  // adjust identifier, if needed
  replace_symbol(type);

  const irep_idt &identifier=
    to_symbol_type(type).get_identifier();

  contextt::symbolst::const_iterator s_it=
    context.symbols.find(identifier);

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
    // overwrite, but preserve (add) any qualifiers
    c_qualifierst c_qualifiers(type);
    c_qualifiers+=c_qualifierst(symbol.type);
    type=symbol.type;
    c_qualifiers.write(type);
  }
    
  // CPROVER extensions
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
  if(type.id()==ID_array)
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
  const irep_idt &base_symbol_identifier,
  typet &type,
  std::list<codet> &code)
{
  if(type.id()==ID_symbol)
  {
    // we need to follow for structs and such, but only once
    irep_idt identifier=to_symbol_type(type).get_identifier();
    if(already_cleaned.insert(identifier).second)
    {
      contextt::symbolst::iterator s_it=context.symbols.find(identifier);
      assert(s_it!=context.symbols.end());
      clean_type(identifier, s_it->second.type, code);
    }
  }
  else if(type.id()==ID_array)
  {
    array_typet &array_type=to_array_type(type);
  
    clean_type(base_symbol_identifier, array_type.subtype(), code);

    // The size need not be a constant!
    // This was simplified already by typecheck_array_type.
    
    exprt &size=array_type.size();
    
    if(size.is_not_nil() &&
       !size.is_constant() &&
       size.id()!=ID_infinity)
    {
      assert(current_symbol_id!=irep_idt());
        
      const symbolt &base_symbol=
        lookup(
          base_symbol_identifier!=irep_idt()?
          base_symbol_identifier:
          current_symbol_id);
      
      // Need to pull out! We insert new symbol.
      locationt location=size.find_location();
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
      new_symbol.is_file_local=true;
      new_symbol.is_type=false;
      new_symbol.value.make_nil();
      new_symbol.location=location;
      context.add(new_symbol);

      // produce the code that initializes the symbol      
      symbol_exprt symbol_expr;
      symbol_expr.set_identifier(temp_identifier);
      symbol_expr.type()=size.type();
      code_assignt assignment;
      assignment.lhs()=symbol_expr;
      assignment.rhs()=size;
      assignment.location()=location;

      // store the code
      code.push_back(assignment);

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
      clean_type(base_symbol_identifier, it->type(), code);
  }
  else if(type.id()==ID_code)
  {
    // done, can't contain arrays
  }
  else if(type.id()==ID_pointer)
  {
    clean_type(base_symbol_identifier, type.subtype(), code);
  }
  else if(type.id()==ID_vector)
  {
    // should be clean
  }
}

