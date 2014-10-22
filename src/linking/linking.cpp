/*******************************************************************\

Module: ANSI-C Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <stack>

#include <util/find_symbols.h>
#include <util/source_location.h>
#include <util/base_type.h>
#include <util/i2string.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/simplify_expr.h>

#include <langapi/language_util.h>

#include "linking.h"
#include "linking_class.h"

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

void linkingt::show_struct_diff(
  const struct_typet &old_type, const struct_typet &new_type)
{
  if(old_type.components().size()!=new_type.components().size())
    str << "number of members is different";
  else
  {
    for(unsigned i=0; i<old_type.components().size(); i++)
    {
      if(old_type.components()[i].get_name()!=new_type.components()[i].get_name())
      {
        str << "name of member differs: "
            << old_type.components()[i].get_name() << " vs. "
            << new_type.components()[i].get_name();
        break;
      }
      
      if(!base_type_eq(old_type.components()[i].type(), new_type.components()[i].type(), ns))
      {
        str << "type of member "
            << old_type.components()[i].get_name() << " differs: "
            << type_to_string(ns, "", old_type.components()[i].type()) << " vs. "
            << type_to_string(ns, "", new_type.components()[i].type());
        str << "\n" << old_type.components()[i].type().pretty() << "\n";
        str << "\n" << new_type.components()[i].type().pretty() << "\n";
        break;
      }
    }
  }
}

void linkingt::link_error(
    const symbolt &old_symbol,
    const symbolt &new_symbol,
    const std::string &msg)
{
  err_location(new_symbol.location);

  str << "error: " << msg << " `"
      << old_symbol.display_name()
      << "'" << "\n";
  str << "old definition in module `" << old_symbol.module
      << "' " << old_symbol.location << "\n"
      << type_to_string_verbose(ns, old_symbol) << "\n";
  str << "new definition in module `" << new_symbol.module
      << "' " << new_symbol.location << "\n"
      << type_to_string_verbose(ns, new_symbol);

  if(ns.follow(old_symbol.type).id()==ID_struct &&
     ns.follow(new_symbol.type).id()==ID_struct)
  {
    str << "\n";
    str << "Difference between struct types:\n";
    show_struct_diff(to_struct_type(ns.follow(old_symbol.type)), 
                     to_struct_type(ns.follow(new_symbol.type)));
  }
  
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

irep_idt linkingt::rename(const irep_idt id)
{
  unsigned cnt=0;

  while(true)
  {
    irep_idt new_identifier=
      id2string(id)+"$link"+i2string(++cnt);

    if(main_symbol_table.symbols.find(new_identifier)!=
       main_symbol_table.symbols.end())
      continue; // already in main symbol table
    
    if(!renamed_ids.insert(new_identifier).second)
      continue; // used this for renaming already

    if(src_symbol_table.symbols.find(new_identifier)!=
       src_symbol_table.symbols.end())
      continue; // used by some earlier linking call already

    return new_identifier;
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

Function: linkingt::duplicate_code_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void linkingt::duplicate_code_symbol(
  symbolt &old_symbol,
  symbolt &new_symbol)
{
  // Both are functions.
  if(!base_type_eq(old_symbol.type, new_symbol.type, ns))
  {
    const code_typet &old_t=to_code_type(old_symbol.type);
    const code_typet &new_t=to_code_type(new_symbol.type);

    // if one of them was an implicit declaration, just issue a warning
    if(!old_symbol.location.get_function().empty() &&
       old_symbol.value.is_nil())
    {
      // issue a warning and overwrite
      link_warning(
        old_symbol,
        new_symbol,
        "implicit function declaration");

      old_symbol.type=new_symbol.type;
      old_symbol.location=new_symbol.location;
    }
    else if(!new_symbol.location.get_function().empty() &&
            new_symbol.value.is_nil())
    {
      // issue a warning
      link_warning(
        old_symbol,
        new_symbol,
        "ignoring conflicting implicit function declaration");
    }
    // handle (incomplete) function prototypes
    else if(base_type_eq(old_t.return_type(), new_t.return_type(), ns) &&
            ((old_t.parameters().empty() && old_t.has_ellipsis()) ||
             (new_t.parameters().empty() && new_t.has_ellipsis())))
    {
      if(old_t.parameters().empty() && old_t.has_ellipsis())
      {
        old_symbol.type=new_symbol.type;
        old_symbol.location=new_symbol.location;
      }
    }
    // mismatch on number of parameters is definitively an error
    else if(old_t.parameters().size()!=new_t.parameters().size())
    {
      link_error(
        old_symbol,
        new_symbol,
        "conflicting parameter counts of function declarations");
    }
    else
    {
      // the number of parameters matches, collect all the conflicts
      // and see whether they can be cured
      std::string warn_msg;
      bool replace=false;
      typedef std::deque<std::pair<typet, typet> > conflictst;
      conflictst conflicts;

      if(!base_type_eq(old_t.return_type(), new_t.return_type(), ns))
        conflicts.push_back(
          std::make_pair(old_t.return_type(), new_t.return_type()));

      code_typet::parameterst::const_iterator n_it=
        new_t.parameters().begin();
      for(code_typet::parameterst::const_iterator
          o_it=old_t.parameters().begin();
          o_it!=old_t.parameters().end();
          ++o_it, ++n_it)
      {
        if(!base_type_eq(o_it->type(), n_it->type(), ns))
          conflicts.push_back(
            std::make_pair(o_it->type(), n_it->type()));
      }

      while(!conflicts.empty())
      {
        const typet &t1=ns.follow(conflicts.front().first);
        const typet &t2=ns.follow(conflicts.front().second);

        // void vs. non-void return type may be acceptable if the
        // return value is never used
        if((t1.id()==ID_empty || t2.id()==ID_empty) &&
           (old_symbol.value.is_nil() || new_symbol.value.is_nil()))
        {
          if(warn_msg.empty())
            warn_msg="void/non-void return type conflict on function";
          replace=
            new_symbol.value.is_not_nil() ||
            (old_symbol.value.is_nil() && t2.id()==ID_empty);
        }
        // different pointer arguments without implementation may work
        else if(t1.id()==ID_pointer && t2.id()==ID_pointer &&
                old_symbol.value.is_nil() && new_symbol.value.is_nil())
        {
          if(warn_msg.empty())
            warn_msg="different pointer types in extern function";
        }
        // different pointer arguments with implementation - the
        // implementation is always right, even though such code may
        // be severely broken
        else if(t1.id()==ID_pointer && t2.id()==ID_pointer &&
                old_symbol.value.is_nil()!=new_symbol.value.is_nil())
        {
          if(warn_msg.empty())
            warn_msg="different pointer types in function";
          replace=new_symbol.value.is_not_nil();
        }
        // transparent union with (or entirely without) implementation is
        // ok -- this primarily helps all those people that don't get
        // _GNU_SOURCE consistent
        else if((t1.id()==ID_union &&
                 (t1.get_bool(ID_C_transparent_union) ||
                  conflicts.front().first.get_bool(ID_C_transparent_union)) &&
                 new_symbol.value.is_nil()) ||
                (t2.id()==ID_union &&
                 (t2.get_bool(ID_C_transparent_union) ||
                  conflicts.front().second.get_bool(ID_C_transparent_union)) &&
                 old_symbol.value.is_nil()))
        {
          const bool use_old=
            t1.id()==ID_union &&
            (t1.get_bool(ID_C_transparent_union) ||
             conflicts.front().first.get_bool(ID_C_transparent_union)) &&
            new_symbol.value.is_nil();

          const union_typet &dest_union_type=
            to_union_type(use_old?t1:t2);
          const typet &src_type=use_old?t2:t1;

          bool found=false;
          for(union_typet::componentst::const_iterator
              it=dest_union_type.components().begin();
              !found && it!=dest_union_type.components().end();
              it++)
            if(base_type_eq(it->type(), src_type, ns))
            {
              found=true;
              if(warn_msg.empty())
                warn_msg="conflict on transparent union parameter in function";
              replace=!use_old;
            }

          if(!found)
            break;
        }
        else
          break;

        conflicts.pop_front();
      }

      if(!conflicts.empty())
        link_error(
          old_symbol,
          new_symbol,
          "conflicting function declarations");
      else
      {
        // warns about the first inconsistency
        link_warning(old_symbol, new_symbol, warn_msg);

        if(replace)
        {
          old_symbol.type=new_symbol.type;
          old_symbol.location=new_symbol.location;
        }
      }
    }
  }

  if(!new_symbol.value.is_nil())
  {
    if(old_symbol.value.is_nil())
    {
      // the one with body wins!
      rename_symbol(new_symbol.value);
      rename_symbol(new_symbol.type);
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

/*******************************************************************\

Function: linkingt::duplicate_object_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void linkingt::duplicate_object_symbol(
  symbolt &old_symbol,
  symbolt &new_symbol)
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
    duplicate_code_symbol(old_symbol, new_symbol);
  else
    duplicate_object_symbol(old_symbol, new_symbol);

  // care about flags

  if(old_symbol.is_extern && !new_symbol.is_extern)
    old_symbol.location=new_symbol.location;

  // it's enough that one isn't extern for the final one not to be
  old_symbol.is_extern=old_symbol.is_extern && new_symbol.is_extern;
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
      rename_symbol.insert_type(*it, new_identifier);
    else
      rename_symbol.insert_expr(*it, new_identifier);
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
  // First apply the renaming
  Forall_symbols(s_it, src_symbol_table.symbols)
  {
    // apply the renaming
    rename_symbol(s_it->second.type);
    rename_symbol(s_it->second.value);
  }

  // Move over all the non-colliding ones
  id_sett collisions;
  
  Forall_symbols(s_it, src_symbol_table.symbols)
  {
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
        collisions.insert(s_it->first);
    }
  }
  
  // Now do the collisions
  for(id_sett::const_iterator
      i_it=collisions.begin();
      i_it!=collisions.end();
      i_it++)
  {
    symbolt &old_symbol=main_symbol_table.symbols[*i_it];
    symbolt &new_symbol=src_symbol_table.symbols[*i_it];
    
    if(new_symbol.is_type)
      duplicate_type_symbol(old_symbol, new_symbol);
    else
      duplicate_non_type_symbol(old_symbol, new_symbol);
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
  
  // PHASE 2: actually rename them
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
