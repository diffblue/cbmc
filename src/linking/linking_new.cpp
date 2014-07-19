/*******************************************************************\

Module: ANSI-C Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <stack>

#include <util/find_symbols.h>
#include <util/location.h>
#include <util/base_type.h>
#include <util/i2string.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/simplify_expr.h>

#include <langapi/language_util.h>

#include "linking.h"
#include "linking_class_new.h"

/*******************************************************************\

Function: linkingt::expr_to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string linkingt::expr_to_string(
  const namespacet &ns,
  const irep_idt &identifier,
  const exprt &expr) const
{ 
  return from_expr(ns, identifier, expr);
}

/*******************************************************************\

Function: linkingt::type_to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string linkingt::type_to_string(
  const namespacet &ns,
  const irep_idt &identifier,
  const typet &type) const
{ 
  return from_type(ns, identifier, type);
}

/*******************************************************************\

Function: linkingt::type_to_string_verbose

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string linkingt::type_to_string_verbose(
  const namespacet &ns,
  const symbolt &symbol,
  const typet &type) const
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
      result+=type_to_string(ns, symbol.name, subtype);
      result+=' ';

      if(it->get_base_name()!="")
        result+=id2string(it->get_base_name());
      else
        result+=id2string(it->get_name());

      result+=";\n";
    }
    
    result+='}';
    
    return result;
  }
  else if(followed.id()==ID_pointer)
  {
    return type_to_string_verbose(ns, symbol, followed.subtype())+" *";
  }
  else if(followed.id()==ID_incomplete_struct ||
          followed.id()==ID_incomplete_union)
  {
    return type_to_string(ns, symbol.name, type)+"   (incomplete)";
  }

  return type_to_string(ns, symbol.name, type);
}

/*******************************************************************\

Function: linkingt::link_error

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void linkingt::link_error(
    const symbolt &old_symbol,
    const symbolt &new_symbol,
    const std::string &msg)
{
  err_location(new_symbol.location);

  str << "error: " << msg << " `"
      << old_symbol.display_name()
      << "'" << std::endl;
  str << "old definition in module `" << old_symbol.module
      << "' " << old_symbol.location << std::endl
      << type_to_string_verbose(ns, old_symbol) << std::endl;
  str << "new definition in module `" << new_symbol.module
      << "' " << new_symbol.location << std::endl
      << type_to_string_verbose(ns, new_symbol);

  throw 0;
}

/*******************************************************************\

Function: linkingt::link_warning

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void linkingt::link_warning(
    const symbolt &old_symbol,
    const symbolt &new_symbol,
    const std::string &msg)
{
  str << "warning: " << msg << " \""
      << old_symbol.display_name()
      << "\"" << std::endl;
  str << "old definition in module " << old_symbol.module
      << " " << old_symbol.location << std::endl
      << type_to_string_verbose(ns, old_symbol) << std::endl;
  str << "new definition in module " << new_symbol.module
      << " " << new_symbol.location << std::endl
      << type_to_string_verbose(ns, new_symbol);

  warning();
}

/*******************************************************************\

Function: linkingt::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt linkingt::rename(irep_idt id)
{
  unsigned cnt=0;

  while(true)
  {
    irep_idt new_identifier=id2string(id)+"$link"+i2string(++cnt);

    if(main_symbol_table.symbols.find(new_identifier)==
       main_symbol_table.symbols.end() &&
       renamed_ids.find(new_identifier)==
       renamed_ids.end())
    {
      renamed_ids.insert(new_identifier);
      return new_identifier;
    }
  }
}

/*******************************************************************\

Function: linkingt::needs_renaming_non_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool linkingt::needs_renaming_non_type(
  const symbolt &old_symbol,
  const symbolt &new_symbol)
{
  // We first take care of file-local non-type symbols.
  // These are static functions, or static variables
  // inside static function bodies.
  if(new_symbol.is_file_local ||
     old_symbol.is_file_local)
    return true;
  
  return false;
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
  // see if it is a function or a variable

  bool is_code_old_symbol=old_symbol.type.id()==ID_code;
  bool is_code_new_symbol=new_symbol.type.id()==ID_code;

  if(is_code_old_symbol!=is_code_new_symbol)
    link_error(
      old_symbol,
      new_symbol,
      "conflicting definition for symbol");

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
        replace_symbol(new_symbol.value);
        replace_symbol(new_symbol.type);
        old_symbol.value=new_symbol.value;
        old_symbol.type=new_symbol.type; // for parameter identifiers
      }
      else if(to_code_type(old_symbol.type).get_inlined())
      {
        // ok, silently ignore
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
        link_error(
          old_symbol,
          new_symbol,
          "duplicate definition of function");
    }
  }
  else
  {
    // both are variables

    if(!base_type_eq(old_symbol.type, new_symbol.type, ns))
    {
      const typet &old_type=ns.follow(old_symbol.type);
      const typet &new_type=ns.follow(new_symbol.type);
    
      if(old_type.id()==ID_array && new_type.id()==ID_array &&
         base_type_eq(old_type.subtype(), new_type.subtype(), ns))
      {
        // still need to compare size
        const exprt &old_size=to_array_type(old_type).size();
        const exprt &new_size=to_array_type(new_type).size();
        
        if(old_size.is_nil() && new_size.is_not_nil())
        {
          old_symbol.type=new_symbol.type; // store new type
        }
        else if(old_size.is_not_nil() && new_size.is_nil())
        {
          // ok, we will use the old type
        }
        else
          link_error(
            old_symbol,
            new_symbol,
            "conflicting array sizes for variable");
      }
      else if(old_type.id()==ID_pointer && new_type.id()==ID_array)
      {
        // store new type
        old_symbol.type=new_symbol.type;
      }
      else if(old_type.id()==ID_array && new_type.id()==ID_pointer)
      {
        // ignore
      }
      else if(old_type.id()==ID_pointer && new_type.id()==ID_pointer)
      {
        link_warning(
          old_symbol,
          new_symbol,
          "conflicting pointer types for variable");
      }
      else if((old_type.id()==ID_incomplete_struct &&
               new_type.id()==ID_struct) ||
              (old_type.id()==ID_incomplete_union &&
               new_type.id()==ID_union))
      {
        // store new type
        old_symbol.type=new_symbol.type;
      }
      else if((old_type.id()==ID_struct &&
               new_type.id()==ID_incomplete_struct) ||
              (old_type.id()==ID_union &&
               new_type.id()==ID_incomplete_union))
      {
        // ignore
      }
      else
      {
        link_error(
          old_symbol,
          new_symbol,
          "conflicting types for variable");
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
          str << "error: conflicting initializers for variable \""
              << old_symbol.name
              << "\"" << std::endl;
          str << "old value in module " << old_symbol.module
              << " " << old_symbol.value.find_location() << std::endl
              << expr_to_string(ns, old_symbol.name, tmp_old) << std::endl;
          str << "new value in module " << new_symbol.module
              << " " << new_symbol.value.find_location() << std::endl
              << expr_to_string(ns, new_symbol.name, tmp_new);
          throw 0;
        }
      }
    }
    
    // care about flags
    
    // it's enough that one isn't extern for the final one not to be
    old_symbol.is_extern=old_symbol.is_extern && new_symbol.is_extern;
  }
}

/*******************************************************************\

Function: linkingt::duplicate_type_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void linkingt::duplicate_type_symbol(
  symbolt &old_symbol,
  symbolt &new_symbol)
{
  assert(new_symbol.is_type);
  
  if(!old_symbol.is_type)
    link_error(
      old_symbol,
      new_symbol,
      "conflicting definition for symbol");

  if(old_symbol.type==new_symbol.type)
    return;

  if(old_symbol.type.id()==ID_incomplete_struct &&
     new_symbol.type.id()==ID_struct)
  {
    old_symbol.type=new_symbol.type;
    old_symbol.location=new_symbol.location;
    return;
  }
  
  if(old_symbol.type.id()==ID_struct &&
     new_symbol.type.id()==ID_incomplete_struct)
  {
    // ok, keep old
    return;
  }
  
  if(old_symbol.type.id()==ID_incomplete_union &&
     new_symbol.type.id()==ID_union)
  {
    old_symbol.type=new_symbol.type;
    old_symbol.location=new_symbol.location;
    return;
  }
  
  if(old_symbol.type.id()==ID_union &&
     new_symbol.type.id()==ID_incomplete_union)
  {
    // ok, keep old
    return;
  }

  if(old_symbol.type.id()==ID_array &&
     new_symbol.type.id()==ID_array &&
     base_type_eq(old_symbol.type.subtype(), new_symbol.type.subtype(), ns))
  {
    if(to_array_type(old_symbol.type).size().is_nil() &&
       to_array_type(new_symbol.type).size().is_not_nil())
    {
      to_array_type(old_symbol.type).size()=
        to_array_type(new_symbol.type).size();
      return;
    }

    if(to_array_type(new_symbol.type).size().is_nil() &&
       to_array_type(old_symbol.type).size().is_not_nil())
    {
      // ok, keep old
      return;
    }
  }

  link_error(
    old_symbol,
    new_symbol,
    "unexpected difference between type symbols");
}

/*******************************************************************\

Function: linkingt::needs_renaming_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool linkingt::needs_renaming_type(
  const symbolt &old_symbol,
  const symbolt &new_symbol)
{
  assert(new_symbol.is_type);
  
  if(!old_symbol.is_type)
    return true;

  if(old_symbol.type==new_symbol.type)
    return false;
  
  if(old_symbol.type.id()==ID_incomplete_struct &&
     new_symbol.type.id()==ID_struct)
    return false; // not different
  
  if(old_symbol.type.id()==ID_struct &&
     new_symbol.type.id()==ID_incomplete_struct)
    return false; // not different
  
  if(old_symbol.type.id()==ID_incomplete_union &&
     new_symbol.type.id()==ID_union)
    return false; // not different
  
  if(old_symbol.type.id()==ID_union &&
     new_symbol.type.id()==ID_incomplete_union)
    return false; // not different

  if(old_symbol.type.id()==ID_array &&
     new_symbol.type.id()==ID_array &&
     base_type_eq(old_symbol.type.subtype(), new_symbol.type.subtype(), ns))
  {
    if(to_array_type(old_symbol.type).size().is_nil() &&
       to_array_type(new_symbol.type).size().is_not_nil())
      return false; // not different

    if(to_array_type(new_symbol.type).size().is_nil() &&
       to_array_type(old_symbol.type).size().is_not_nil())
      return false; // not different
  }
  
  return true; // different
}

/*******************************************************************\

Function: linkingt::do_type_dependencies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void linkingt::do_type_dependencies(id_sett &needs_to_be_renamed)
{
  // Any type that uses a type that will be renamed also
  // needs to be renamed, and so on, until saturation.

  used_byt used_by;

  forall_symbols(s_it, src_symbol_table.symbols)
  {
    if(s_it->second.is_type)
    {
      find_symbols_sett type_symbols_used;
      find_type_symbols(s_it->second.type, type_symbols_used);

      for(find_symbols_sett::const_iterator
          it=type_symbols_used.begin();
          it!=type_symbols_used.end();
          it++)
      {
        used_by[*it].insert(s_it->first);
      }
    }
  }

  std::stack<irep_idt> queue;

  for(id_sett::const_iterator
      d_it=needs_to_be_renamed.begin();
      d_it!=needs_to_be_renamed.end();
      d_it++)
    queue.push(*d_it);

  while(!queue.empty())
  {
    irep_idt id=queue.top();
    queue.pop();

    const id_sett &u=used_by[id];

    for(id_sett::const_iterator
        d_it=u.begin();
        d_it!=u.end();
        d_it++)
      if(needs_to_be_renamed.insert(*d_it).second)
      {
        queue.push(*d_it);
        #ifdef DEBUG
        str << "LINKING: needs to be renamed (dependency): " << s_it->first;
        debug();
        #endif
      }
  }
}
  
/*******************************************************************\

Function: linkingt::rename_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void linkingt::rename_symbols(const id_sett &needs_to_be_renamed)
{
  for(id_sett::const_iterator
      it=needs_to_be_renamed.begin();
      it!=needs_to_be_renamed.end();
      it++)
  {
    symbolt &new_symbol=src_symbol_table.symbols[*it];

    irep_idt new_identifier=rename(*it);
    new_symbol.name=new_identifier;
    
    #ifdef DEBUG
    str << "LINKING: renaming " << *it << " to "
        << new_identifier;
    debug();
    #endif

    if(new_symbol.is_type)
      replace_symbol.insert_type(*it, new_identifier);
    else
      replace_symbol.insert_expr(*it, new_identifier);
  }
}

/*******************************************************************\

Function: linkingt::copy_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void linkingt::copy_symbols()
{
  Forall_symbols(s_it, src_symbol_table.symbols)
  {
    // apply the replacement map
    replace_symbol(s_it->second.type);
    replace_symbol(s_it->second.value);
  
    // renamed?
    if(s_it->first!=s_it->second.name)
    {
      // new
      main_symbol_table.add(s_it->second);
    }
    else
    {
      symbol_tablet::symbolst::iterator
        m_it=main_symbol_table.symbols.find(s_it->first);
    
      if(m_it==main_symbol_table.symbols.end())
      {
        // new
        main_symbol_table.add(s_it->second);
      }
      else
      {
        // duplicate
        if(s_it->second.is_type)
          duplicate_type_symbol(m_it->second, s_it->second);
        else
          duplicate_non_type_symbol(m_it->second, s_it->second);
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
  // We do this in three phases. We first figure out which symbols need to
  // be renamed, and then build the renaming, and finally apply this
  // renaming in the second pass over the symbol table.
  
  // PHASE 1: identify symbols to be renamed
  
  id_sett needs_to_be_renamed;
  
  forall_symbols(s_it, src_symbol_table.symbols)
  {
    symbol_tablet::symbolst::const_iterator
      m_it=main_symbol_table.symbols.find(s_it->first);
  
    if(m_it!=main_symbol_table.symbols.end() && // duplicate
       needs_renaming(m_it->second, s_it->second))
    {
      needs_to_be_renamed.insert(s_it->first);
      #ifdef DEBUG
      str << "LINKING: needs to be renamed: " << s_it->first;
      debug();
      #endif
    }
  }
  
  // renaming types may trigger further renaming
  do_type_dependencies(needs_to_be_renamed);
  
  // PHASE 2: rename them
  rename_symbols(needs_to_be_renamed);

  // PHASE 3: copy new symbols to main table
  copy_symbols();
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
