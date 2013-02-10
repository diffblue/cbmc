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
#include <simplify_expr.h>

#include <ansi-c/expr2c.h>

#include "linking_type_eq.h"

#include "linking.h"
#include "linking_class.h"

/*******************************************************************\

Function: linkingt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string linkingt::to_string(const exprt &expr)
{ 
  return expr2c(expr, ns);
}

/*******************************************************************\

Function: linkingt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string linkingt::to_string(const typet &type)
{ 
  return type2c(type, ns);
}

/*******************************************************************\

Function: linkingt::to_string_verbose

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string linkingt::to_string_verbose(const typet &type)
{ 
  const typet &followed=ns.follow(type);

  if(followed.id()==ID_struct || followed.id()==ID_union)
  {
    std::string result=followed.id_string();

    const std::string &tag=followed.get_string(ID_tag);
    if(tag!="") result+=" "+tag;
    result+=" {\n";
    
    const struct_union_typet::componentst &components=
      to_struct_union_type(followed).components();

    for(struct_union_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      const typet &subtype=it->type();
      result+="  ";
      result+=to_string(subtype);
      result+=" ";

      if(it->get_base_name()!="")
        result+=id2string(it->get_base_name());
      else
        result+=id2string(it->get_name());

      result+=";\n";
    }
    
    result+="}";
    
    return result;
  }
  else if(followed.id()==ID_pointer)
  {
    return to_string_verbose(followed.subtype())+" *";
  }

  return to_string(type);
}

/*******************************************************************\

Function: linkingt::duplicate_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void linkingt::duplicate_symbol(
  symbolt &old_symbol,
  symbolt &new_symbol)
{
  if(new_symbol.is_file_local ||
      (!new_symbol.is_type && !old_symbol.is_type))
    duplicate_non_type_symbol(old_symbol, new_symbol);
  else if(new_symbol.is_type && old_symbol.is_type)
  {
    bool move=true;
    duplicate_type_symbol(old_symbol, new_symbol, move);
  }
  else if(new_symbol.is_type && old_symbol.is_file_local)
    rename_type_symbol(new_symbol);
  else
  {
    str << "symbol category conflict on symbol `"
      << old_symbol.name << "'";
    throw 0;
  }
}

/*******************************************************************\

Function: linkingt::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt linkingt::rename(const irep_idt &old_identifier)
{
  irep_idt new_identifier;
    
  do
  {
    new_identifier=
      id2string(old_identifier)+"$link"+i2string(renaming_counter++);        
  }
  while(main_symbol_table.symbols.find(new_identifier)!=
        main_symbol_table.symbols.end() ||
        src_symbol_table.symbols.find(new_identifier)!=
        src_symbol_table.symbols.end());
        
  return new_identifier;
}

/*******************************************************************\

Function: linkingt::rename_type_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void linkingt::rename_type_symbol(symbolt &new_symbol)
{
  replace_symbolt::type_mapt::const_iterator replace_entry=
    replace_symbol.type_map.find(new_symbol.name);

  if(replace_entry!=replace_symbol.type_map.end())
  {
    new_symbol.name=to_symbol_type(replace_entry->second).get_identifier();
  }
  else
  {
    // rename!
    irep_idt old_identifier=new_symbol.name;
    irep_idt new_identifier=rename(old_identifier);

    replace_symbol.insert(old_identifier, symbol_typet(new_identifier));

    new_symbol.name=new_identifier;
  }

  // need to replace again
  replace_symbol.replace(new_symbol.type);

  // move over!
  bool result=main_symbol_table.move(new_symbol);
  assert(!result);
}

/*******************************************************************\

Function: linkingt::duplicate_type_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void linkingt::duplicate_type_symbol(
  symbolt &old_symbol,
  symbolt &new_symbol,
  bool &move)
{
  // check if it is really the same
  // -- use base_type_eq, not linking_type_eq
  // first make sure that base_type_eq can soundly use ns/main_symbol_table only
  find_symbols_sett symbols;
  find_type_and_expr_symbols(new_symbol.type, symbols);
  bool ok=true;
  for(find_symbols_sett::const_iterator
      s_it=symbols.begin();
      ok && s_it!=symbols.end();
      s_it++)
    ok&=completed.find(*s_it)!=completed.end();
  if(ok && base_type_eq(old_symbol.type, new_symbol.type, ns))
  {
    move=false;
    return;
  }

  // they are different
  if(old_symbol.type.id()==ID_incomplete_struct &&
     new_symbol.type.id()==ID_struct)
  {
    if(move)
      old_symbol.type=new_symbol.type; // store new type
    move=false;
  }
  else if(old_symbol.type.id()==ID_struct &&
          new_symbol.type.id()==ID_incomplete_struct)
  {
    // ignore
    move=false;
  }
  else if(ns.follow(old_symbol.type).id()==ID_array &&
          ns.follow(new_symbol.type).id()==ID_array)
  {
    if(move &&
       to_array_type(ns.follow(old_symbol.type)).size().is_nil() &&
       to_array_type(ns.follow(new_symbol.type)).size().is_not_nil())
      old_symbol.type=new_symbol.type; // store new type
    move=false;
  }
  else
  {
    if(move)
      rename_type_symbol(new_symbol);
    move=true;
  }
}

/*******************************************************************\

Function: linkingt::duplicate_non_type_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void linkingt::duplicate_non_type_symbol(
  symbolt &old_symbol,
  symbolt &new_symbol)
{
  // We first take care of file-local non-type symbols.
  // These are static functions, or static variables
  // inside function bodies.
  if(new_symbol.is_file_local ||
     old_symbol.is_file_local)
  {
    // we just always rename these
    irep_idt old_identifier=new_symbol.name;
    irep_idt new_identifier=rename(old_identifier);
    replace_symbol.insert(
        old_identifier,
        symbol_exprt(new_identifier, new_symbol.type));

    new_symbol.name=new_identifier;
    
    // move over!
    bool result=main_symbol_table.move(new_symbol);
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
      if(ns.follow(old_symbol.type).id()==ID_array &&
         ns.follow(new_symbol.type).id()==ID_array)
      {
        if(to_array_type(ns.follow(old_symbol.type)).size().is_nil() &&
           to_array_type(ns.follow(new_symbol.type)).size().is_not_nil())
          old_symbol.type=new_symbol.type; // store new type
      }
      else if(ns.follow(old_symbol.type).id()==ID_pointer &&
              ns.follow(new_symbol.type).id()==ID_array)
      {
        // store new type
        old_symbol.type=new_symbol.type;
      }
      else if(ns.follow(old_symbol.type).id()==ID_array &&
              ns.follow(new_symbol.type).id()==ID_pointer)
      {
        // ignore
      }
      else if(ns.follow(old_symbol.type).id()==ID_pointer &&
              ns.follow(new_symbol.type).id()==ID_pointer)
      {
        // ignore, generally ok
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
      else
      {
        err_location(new_symbol.location);
        str << "error: conflicting definition for variable `"
            << old_symbol.name
            << "'" << std::endl;
        str << "old definition: " << to_string_verbose(old_symbol.type)
            << std::endl;
        str << "Module: " << old_symbol.module << std::endl;
        str << "new definition: " << to_string_verbose(new_symbol.type)
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
      else
      {
        // try simplifier
        exprt tmp_old=old_symbol.value,
              tmp_new=new_symbol.value;
              
        simplify(tmp_old, ns);
        simplify(tmp_new, ns);
        
        if(base_type_eq(tmp_old, tmp_new, ns))
        {
          // ok, the same
        }
        else
        {
          err_location(new_symbol.value);
          str << "error: conflicting initializers for variable `"
              << old_symbol.name
              << "'" << std::endl;
          str << "old value: " << to_string(tmp_old)
              << std::endl;
          str << "Module: " << old_symbol.module << std::endl;
          str << "new value: " << to_string(tmp_new)
              << std::endl;
          str << "Module: " << new_symbol.module;
          throw 0;
        }
      }
    }
  }
}

/*******************************************************************\

Function: linkingt::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void linkingt::typecheck()
{
  // we inspect all the symbols in src_symbol_table
  
  forall_symbols(it, src_symbol_table.symbols)
    inspect_src_symbol(it->first);
}

/*******************************************************************\

Function: linkingt::inspect_src_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void linkingt::inspect_src_symbol(const irep_idt &identifier)
{
  // is it done already?
  if(completed.find(identifier)!=completed.end())
    return;

  // look it up, it must be there
  symbolt &new_symbol=src_symbol_table.lookup(identifier);

  // resolve recursion on types; we shouldn't need specific care
  // for non-types even though recursion may occur via initializers
  if(!processing.insert(identifier).second)
  {
    if(!main_symbol_table.has_symbol(identifier))
      return;

    symbolt &old_symbol=main_symbol_table.lookup(identifier);
    bool move=false;
    if(new_symbol.is_type && old_symbol.is_type)
      duplicate_type_symbol(old_symbol, new_symbol, move);

    if(move)
    {
      irep_idt old_identifier=new_symbol.name;
      irep_idt new_identifier=rename(old_identifier);

      replace_symbol.insert(old_identifier, symbol_typet(new_identifier));
    }

    return;
  }

  // first find out what symbols this uses
  find_symbols_sett symbols;
  find_type_and_expr_symbols(new_symbol.value, symbols);
  find_type_and_expr_symbols(new_symbol.type, symbols);
  // also add function arguments
  if(new_symbol.type.id()==ID_code)
  {
    const code_typet &code_type=to_code_type(new_symbol.type);
    const code_typet::argumentst &arguments=code_type.arguments();

    for(code_typet::argumentst::const_iterator
        it=arguments.begin();
        it!=arguments.end();
        it++)
      // identifiers for prototypes need not exist
      if(!it->get_identifier().empty() &&
          src_symbol_table.has_symbol(it->get_identifier()))
        symbols.insert(it->get_identifier());
  }

  // make sure we inspect those first!
  for(find_symbols_sett::const_iterator
      s_it=symbols.begin();
      s_it!=symbols.end();
      s_it++)
    inspect_src_symbol(*s_it);
    
  // first order of business is to apply renaming
  replace_symbol.replace(new_symbol.value);
  replace_symbol.replace(new_symbol.type);        
  // also rename function arguments, if necessary
  if(new_symbol.type.id()==ID_code)
  {
    code_typet &code_type=to_code_type(new_symbol.type);
    code_typet::argumentst &arguments=code_type.arguments();

    for(code_typet::argumentst::iterator
        it=arguments.begin();
        it!=arguments.end();
        it++)
    {
      replace_symbolt::expr_mapt::const_iterator r=
        replace_symbol.expr_map.find(it->get_identifier());
      if(r!=replace_symbol.expr_map.end())
        it->set_identifier(to_symbol_expr(r->second).get_identifier());
    }
  }
    
  // any symbols contained in new_symbol are now renamed within src_symbol_table and
  // the (possibly renamed) contained symbols are in main_symbol_table
  // any checks for duplicates are now safe to exclusively use lookups on
  // main_symbol_table (via ns)

  // ok, now check if we are to expect a collision
  const symbol_tablet::symbolst::iterator main_s_it=
    main_symbol_table.symbols.find(identifier);
    
  if(main_s_it!=main_symbol_table.symbols.end())
    duplicate_symbol(main_s_it->second, new_symbol); // handle the collision
  else
  {
    // add into destination symbol_table -- should never fail,
    // as there is no collision
    
    bool result=main_symbol_table.move(new_symbol);
    assert(!result);    
  }

  // symbol is really done and can now be used within main_symbol_table
  completed.insert(identifier);
  processing.erase(identifier);
}

/*******************************************************************\

Function: linking

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool linking(
  symbol_tablet &dest_symbol_table,
  symbol_tablet &new_symbol_table,
  message_handlert &message_handler)
{
  linkingt linking(
    dest_symbol_table, new_symbol_table, message_handler);
  
  return linking.typecheck_main();
}
