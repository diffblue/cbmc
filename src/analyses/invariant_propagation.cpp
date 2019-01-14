/*******************************************************************\

Module: Invariant Propagation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Invariant Propagation

#include "invariant_propagation.h"

#include <util/simplify_expr.h>
#include <util/base_type.h>
#include <util/symbol_table.h>
#include <util/std_expr.h>

void invariant_propagationt::make_all_true()
{
  for(auto &state : state_map)
    state.second.invariant_set.make_true();
}

void invariant_propagationt::make_all_false()
{
  for(auto &state : state_map)
    state.second.invariant_set.make_false();
}

void invariant_propagationt::add_objects(
  const goto_programt &goto_program)
{
  // get the globals
  object_listt globals;
  get_globals(globals);

  // get the locals
  goto_programt::decl_identifierst locals;
  goto_program.get_decl_identifiers(locals);

  // cache the list for the locals to speed things up
  typedef std::unordered_map<irep_idt, object_listt> object_cachet;
  object_cachet object_cache;

  forall_goto_program_instructions(i_it, goto_program)
  {
    #if 0
    invariant_sett &is=(*this)[i_it].invariant_set;

    is.add_objects(globals);
    #endif

    for(const auto &local : locals)
    {
      // cache hit?
      object_cachet::const_iterator e_it=object_cache.find(local);

      if(e_it==object_cache.end())
      {
        const symbolt &symbol=ns.lookup(local);

        object_listt &objects=object_cache[local];
        get_objects(symbol, objects);
        #if 0
        is.add_objects(objects);
        #endif
      }
      #if 0
      else
        is.add_objects(e_it->second);
      #endif
    }
  }
}

void invariant_propagationt::get_objects(
  const symbolt &symbol,
  object_listt &dest)
{
  std::list<exprt> object_list;

  get_objects_rec(symbol.symbol_expr(), object_list);

  for(const auto &expr : object_list)
    dest.push_back(object_store.add(expr));
}

void invariant_propagationt::get_objects_rec(
  const exprt &src,
  std::list<exprt> &dest)
{
  const typet &t = src.type();

  if(
    t.id() == ID_struct || t.id() == ID_union || t.id() == ID_struct_tag ||
    t.id() == ID_union_tag)
  {
    const struct_union_typet &struct_type = to_struct_union_type(ns.follow(t));

    for(const auto &component : struct_type.components())
    {
      const member_exprt member_expr(
        src, component.get_name(), component.type());
      // recursive call
      get_objects_rec(member_expr, dest);
    }
  }
  else if(t.id()==ID_array)
  {
    // get_objects_rec(identifier, suffix+"[]", t.subtype(), dest);
    // we don't track these
  }
  else if(check_type(t))
  {
    dest.push_back(src);
  }
}

void invariant_propagationt::add_objects(
  const goto_functionst &goto_functions)
{
  // get the globals
  object_listt globals;
  get_globals(globals);

  forall_goto_functions(f_it, goto_functions)
  {
    // get the locals
    std::set<irep_idt> locals;
    get_local_identifiers(f_it->second, locals);

    const goto_programt &goto_program=f_it->second.body;

    // cache the list for the locals to speed things up
    typedef std::unordered_map<irep_idt, object_listt> object_cachet;
    object_cachet object_cache;

    forall_goto_program_instructions(i_it, goto_program)
    {
      #if 0
      invariant_sett &is=(*this)[i_it].invariant_set;

      is.add_objects(globals);
      #endif

      for(const auto &local : locals)
      {
        // cache hit?
        object_cachet::const_iterator e_it=object_cache.find(local);

        if(e_it==object_cache.end())
        {
          const symbolt &symbol=ns.lookup(local);

          object_listt &objects=object_cache[local];
          get_objects(symbol, objects);
          #if 0
          is.add_objects(objects);
          #endif
        }
        #if 0
        else
          is.add_objects(e_it->second);
        #endif
      }
    }
  }
}

void invariant_propagationt::get_globals(
  object_listt &dest)
{
  // static ones
  for(const auto &symbol_pair : ns.get_symbol_table().symbols)
  {
    if(symbol_pair.second.is_lvalue && symbol_pair.second.is_static_lifetime)
    {
      get_objects(symbol_pair.second, dest);
    }
  }
}

bool invariant_propagationt::check_type(const typet &type) const
{
  if(type.id()==ID_pointer)
    return true;
  else if(
    type.id() == ID_struct || type.id() == ID_union ||
    type.id() == ID_struct_tag || type.id() == ID_union_tag)
    return false;
  else if(type.id()==ID_array)
    return false;
  else if(type.id() == ID_symbol_type)
    return check_type(ns.follow(type));
  else if(type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv)
    return true;
  else if(type.id()==ID_bool)
    return true;

  return false;
}

void invariant_propagationt::initialize(const goto_programt &goto_program)
{
  baset::initialize(goto_program);

  forall_goto_program_instructions(it, goto_program)
  {
    invariant_sett &s = (*this)[it].invariant_set;

    if(it==goto_program.instructions.begin())
      s.make_true();
    else
      s.make_false();

    s.set_value_sets(value_sets);
    s.set_object_store(object_store);
    s.set_namespace(ns);
  }

  add_objects(goto_program);
}

void invariant_propagationt::initialize(const goto_functionst &goto_functions)
{
  baset::initialize(goto_functions);

  forall_goto_functions(f_it, goto_functions)
    initialize(f_it->second.body);
}

void invariant_propagationt::simplify(goto_functionst &goto_functions)
{
  Forall_goto_functions(it, goto_functions)
    simplify(it->second.body);
}

void invariant_propagationt::simplify(goto_programt &goto_program)
{
  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(!i_it->is_assert())
      continue;

    // find invariant set
    const auto &d = (*this)[i_it];
    if(d.is_bottom())
      continue;

    const invariant_sett &invariant_set = d.invariant_set;

    exprt simplified_guard(i_it->guard);

    invariant_set.simplify(simplified_guard);
    ::simplify(simplified_guard, ns);

    if(invariant_set.implies(simplified_guard).is_true())
      i_it->guard=true_exprt();
  }
}
