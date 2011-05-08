/*******************************************************************\

Module: ANSI-C Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <find_symbols.h>
#include <location.h>
#include <base_type.h>
#include <i2string.h>
#include <std_expr.h>
#include <std_types.h>

#include "c_link_type_eq.h"
#include "expr2c.h"

#include "c_link.h"
#include "c_link_class.h"

/*******************************************************************\

Function: c_linkt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string c_linkt::to_string(const exprt &expr)
{ 
  return expr2c(expr, ns);
}

/*******************************************************************\

Function: c_linkt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string c_linkt::to_string(const typet &type)
{ 
  return type2c(type, ns);
}

/*******************************************************************\

Function: c_linkt::duplicate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_linkt::duplicate(
  symbolt &old_symbol,
  symbolt &new_symbol)
{
  if(new_symbol.is_type!=old_symbol.is_type)
  {
    str << "symbol category conflict on symbol `"
        << old_symbol.name << "'";
    throw 0;
  }

  if(new_symbol.is_type)
    duplicate_type(old_symbol, new_symbol);
  else
    duplicate_non_type(old_symbol, new_symbol);
}

/*******************************************************************\

Function: c_linkt::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt c_linkt::rename(const irep_idt &old_identifier)
{
  irep_idt new_identifier;
    
  do
  {
    new_identifier=
      id2string(old_identifier)+"#link"+i2string(renaming_counter++);        
  }
  while(main_context.symbols.find(new_identifier)!=
        main_context.symbols.end());
        
  return new_identifier;
}

/*******************************************************************\

Function: c_linkt::duplicate_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_linkt::duplicate_type(
  symbolt &old_symbol,
  symbolt &new_symbol)
{
  // check if it is really the same
  // -- use base_type_eq, not c_link_type_eq
  if(base_type_eq(old_symbol.type, new_symbol.type, ns))
    return;

  // they are different
  if(old_symbol.type.id()==ID_incomplete_struct &&
     new_symbol.type.id()==ID_struct)
  {
    old_symbol.type=new_symbol.type; // store new type
  }
  else if(old_symbol.type.id()==ID_struct &&
          new_symbol.type.id()==ID_incomplete_struct)
  {
    // ignore
  }
  else if(ns.follow(old_symbol.type).id()==ID_incomplete_array &&
          ns.follow(new_symbol.type).id()==ID_array)
  {
    old_symbol.type=new_symbol.type; // store new type
  }
  else if(ns.follow(old_symbol.type).id()==ID_array &&
          ns.follow(new_symbol.type).id()==ID_incomplete_array)
  {
    // ignore
  }
  else
  {
    // rename!
    irep_idt old_identifier=new_symbol.name;
    irep_idt new_identifier=rename(old_identifier);
              
    replace_symbol.insert(old_identifier, symbol_typet(new_identifier));

    new_symbol.name=new_identifier;
    
    // need to replace again
    replace_symbol.replace(new_symbol.type);
    
    // move over!
    bool result=main_context.move(new_symbol);
    assert(!result);
  }
}

/*******************************************************************\

Function: c_linkt::duplicate_non_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_linkt::duplicate_non_type(
  symbolt &old_symbol,
  symbolt &new_symbol)
{
  // first check if file-local
  if(new_symbol.file_local)
  {
    // we just always rename these
    irep_idt old_identifier=new_symbol.name;
    replace_symbolt::expr_mapt::const_iterator r_it=
      replace_symbol.expr_map.find(old_identifier);
    assert(r_it!=replace_symbol.expr_map.end());
    assert(r_it->second.id()==ID_symbol);

    new_symbol.name=r_it->second.get(ID_identifier);
    
    // move over!
    bool result=main_context.move(new_symbol);
    assert(!result);
    
    return;
  }
  
  // see if it is a function or a variable

  bool is_code_old_symbol=old_symbol.type.id()==ID_code;
  bool is_code_new_symbol=new_symbol.type.id()==ID_code;

  if(is_code_old_symbol!=is_code_new_symbol)
  {
    err_location(new_symbol.location);
    str << "error: conflicting definition for symbol \""
        << old_symbol.display_name()
        << "\"" << std::endl;
    str << "old definition: " << to_string(old_symbol.type)
        << std::endl;
    str << "Module: " << old_symbol.module << std::endl;
    str << "new definition: " << to_string(new_symbol.type)
        << std::endl;
    str << "Module: " << new_symbol.module;
    throw 0;
  }

  if(is_code_old_symbol)
  {
    // Both are functions.
    // We don't compare the types, they will be too different;
    // we just care about the code

    if(!new_symbol.value.is_nil())
    {
      if(old_symbol.value.is_nil())
      {
        // the one with body wins!
        old_symbol.value=new_symbol.value;
        old_symbol.type=new_symbol.type; // for argument identifiers
      }
      else if(to_code_type(old_symbol.type).get_inlined())
      {
        // ok
      }
      else if(base_type_eq(old_symbol.type, new_symbol.type, ns))
      {
        // keep the one in old_symbol -- libraries come last!
        str << "warning: function `" << old_symbol.name << "' in module `" << 
          new_symbol.module << "' is shadowed by a definition in module `" << 
          old_symbol.module << "'";
        warning();
      }
      else
      {
        err_location(new_symbol.value);
        str << "error: duplicate definition of function `"
            << old_symbol.name
            << "'" << std::endl;
        str << "In module `" << old_symbol.module
            << "' and module `" << new_symbol.module << "'";
        throw 0;
      }
    }
  }
  else
  {
    // both are variables

    if(!base_type_eq(old_symbol.type, new_symbol.type, ns))
    {
      if(ns.follow(old_symbol.type).id()==ID_incomplete_array &&
         ns.follow(new_symbol.type).id()==ID_array)
      {
        // store new type
        old_symbol.type=new_symbol.type;
      }
      else if(ns.follow(old_symbol.type).id()==ID_array &&
              ns.follow(new_symbol.type).id()==ID_incomplete_array)
      {
        // ignore
      }
      else if(old_symbol.type.id()==ID_incomplete_struct &&
              new_symbol.type.id()==ID_struct)
      {
        // store new type
        old_symbol.type=new_symbol.type;
      }
      else if(old_symbol.type.id()==ID_struct &&
              new_symbol.type.id()==ID_incomplete_struct)
      {
        // ignore
      }
      else if(ns.follow(old_symbol.type).id()==ID_pointer &&
              ns.follow(new_symbol.type).id()==ID_incomplete_array)
      {
        // ignore
      }
      else
      {
        err_location(new_symbol.location);
        str << "error: conflicting definition for variable `"
            << old_symbol.name
            << "'" << std::endl;
        str << "old definition: " << to_string(old_symbol.type)
            << std::endl;
        str << "Module: " << old_symbol.module << std::endl;
        str << "new definition: " << to_string(new_symbol.type)
            << std::endl;
        str << "Module: " << new_symbol.module;
        throw 0;
      }
    }

    // care about initializers    

    if(!new_symbol.value.is_nil() &&
       !new_symbol.value.get_bool(ID_C_zero_initializer))
    {
      if(old_symbol.value.is_nil() ||
         old_symbol.value.get_bool(ID_C_zero_initializer))
      {
        // new_symbol wins
        old_symbol.value=new_symbol.value;
      }
      else if(!base_type_eq(old_symbol.value, new_symbol.value, ns))
      {
        err_location(new_symbol.value);
        str << "error: conflicting initializers for variable `"
            << old_symbol.name
            << "'" << std::endl;
        str << "old value: " << to_string(old_symbol.value)
            << std::endl;
        str << "Module: " << old_symbol.module << std::endl;
        str << "new value: " << to_string(new_symbol.value)
            << std::endl;
        str << "Module: " << new_symbol.module;
        throw 0;
      }
    }
  }
}

/*******************************************************************\

Function: c_linkt::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_linkt::typecheck()
{
  // we first take care of file-local non-type symbols
  forall_symbols(it, src_context.symbols)
    if(it->second.file_local && !it->second.is_type &&
       main_context.symbols.find(it->first)!=main_context.symbols.end())
    {
      // collision!
      irep_idt new_identifier=rename(it->first);
      replace_symbol.insert(
        it->first, symbol_exprt(new_identifier, it->second.type));
    }

  // we inspect all the symbols in src_context
  
  forall_symbols(it, src_context.symbols)
    inspect_symbol(it->first);
}

/*******************************************************************\

Function: c_linkt::inspect_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_linkt::inspect_symbol(const irep_idt &identifier)
{
  // are we doing it already?
  if(!processing.insert(identifier).second)
    return;

  // look it up, it must be there
  symbolt &new_symbol=src_context.lookup(identifier);
  
  // first find out what symbols this uses
  find_symbols_sett symbols;
  find_type_and_expr_symbols(new_symbol.type, symbols);

  // make sure we inspect those first!
  for(find_symbols_sett::const_iterator
      s_it=symbols.begin();
      s_it!=symbols.end();
      s_it++)
    inspect_symbol(*s_it);
    
  // first order of business is to apply renaming
  replace_symbol.replace(new_symbol.value);
  replace_symbol.replace(new_symbol.type);        
    
  // ok, now check if we are to expect a collision
  const contextt::symbolst::iterator main_s_it=
    main_context.symbols.find(identifier);
    
  if(main_s_it!=main_context.symbols.end())
    duplicate(main_s_it->second, new_symbol); // handle the collision
  else
  {
    // add into dest context -- should never fail,
    // as there is no collision
    
    bool result=main_context.move(new_symbol);
    assert(!result);    
  }
}

/*******************************************************************\

Function: convert_c

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool c_link(
  contextt &dest_context,
  contextt &new_context,
  message_handlert &message_handler)
{
  c_linkt c_link(
    dest_context, new_context, message_handler);
  
  return c_link.typecheck_main();
}
