/*******************************************************************\

Module: Value Set Propagation (Flow Insensitive)

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

/// \file
/// Value Set Propagation (Flow Insensitive)

#include "value_set_analysis_fi.h"

#include <util/prefix.h>
#include <util/cprover_prefix.h>
#include <util/xml_irep.h>
#include <util/symbol_table.h>

#include <langapi/language_util.h>

void value_set_analysis_fit::initialize(
  const goto_programt &goto_program)
{
  baset::initialize(goto_program);
  add_vars(goto_program);
}

void value_set_analysis_fit::initialize(
  const goto_functionst &goto_functions)
{
  baset::initialize(goto_functions);
  add_vars(goto_functions);
}

void value_set_analysis_fit::add_vars(
  const goto_programt &goto_program)
{
  typedef std::list<value_set_fit::entryt> entry_listt;

  // get the globals
  entry_listt globals;
  get_globals(globals);

  // get the locals
  goto_programt::decl_identifierst locals;
  goto_program.get_decl_identifiers(locals);

  // cache the list for the locals to speed things up
  typedef std::unordered_map<irep_idt, entry_listt> entry_cachet;
  entry_cachet entry_cache;

  value_set_fit &v=state.value_set;

  for(goto_programt::instructionst::const_iterator
      i_it=goto_program.instructions.begin();
      i_it!=goto_program.instructions.end();
      i_it++)
  {
    v.add_vars(globals);

    for(goto_programt::decl_identifierst::const_iterator
        l_it=locals.begin();
        l_it!=locals.end();
        l_it++)
    {
      // cache hit?
      entry_cachet::const_iterator e_it=entry_cache.find(*l_it);

      if(e_it==entry_cache.end())
      {
        const symbolt &symbol=ns.lookup(*l_it);

        std::list<value_set_fit::entryt> &entries=entry_cache[*l_it];
        get_entries(symbol, entries);
        v.add_vars(entries);
      }
      else
        v.add_vars(e_it->second);
    }
  }
}

void value_set_analysis_fit::get_entries(
  const symbolt &symbol,
  std::list<value_set_fit::entryt> &dest)
{
  get_entries_rec(symbol.name, "", symbol.type, dest);
}

void value_set_analysis_fit::get_entries_rec(
  const irep_idt &identifier,
  const std::string &suffix,
  const typet &type,
  std::list<value_set_fit::entryt> &dest)
{
  const typet &t=ns.follow(type);

  if(t.id()==ID_struct ||
     t.id()==ID_union)
  {
    for(const auto &c : to_struct_union_type(t).components())
    {
      get_entries_rec(
        identifier, suffix + "." + id2string(c.get_name()), c.type(), dest);
    }
  }
  else if(t.id()==ID_array)
  {
    get_entries_rec(identifier, suffix+"[]", t.subtype(), dest);
  }
  else if(check_type(t))
  {
    dest.push_back(value_set_fit::entryt(identifier, suffix));
  }
}

void value_set_analysis_fit::add_vars(
  const goto_functionst &goto_functions)
{
  // get the globals
  std::list<value_set_fit::entryt> globals;
  get_globals(globals);

  value_set_fit &v=state.value_set;
  v.add_vars(globals);

  forall_goto_functions(f_it, goto_functions)
  {
    // get the locals
    std::set<irep_idt> locals;
    get_local_identifiers(f_it->second, locals);

    for(auto l : locals)
    {
      const symbolt &symbol=ns.lookup(l);

      std::list<value_set_fit::entryt> entries;
      get_entries(symbol, entries);
      v.add_vars(entries);
    }
  }
}

void value_set_analysis_fit::get_globals(
  std::list<value_set_fit::entryt> &dest)
{
  // static ones
  for(const auto &symbol_pair : ns.get_symbol_table().symbols)
  {
    if(symbol_pair.second.is_lvalue && symbol_pair.second.is_static_lifetime)
    {
      get_entries(symbol_pair.second, dest);
    }
  }
}

bool value_set_analysis_fit::check_type(const typet &type)
{
  if(type.id()==ID_pointer)
  {
    switch(track_options)
    {
      case TRACK_ALL_POINTERS:
        { return true; break; }
      case TRACK_FUNCTION_POINTERS:
      {
        if(type.id()==ID_pointer)
        {
          const typet *t = &type;
          while(t->id()==ID_pointer) t = &(t->subtype());

          return (t->id()==ID_code);
        }

        break;
      }
      default: // don't track.
        break;
    }
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union)
  {
    for(const auto &c : to_struct_union_type(type).components())
    {
      if(check_type(c.type()))
        return true;
    }
  }
  else if(type.id()==ID_array)
    return check_type(type.subtype());
  else if(type.id()==ID_symbol)
    return check_type(ns.follow(type));

  return false;
}
