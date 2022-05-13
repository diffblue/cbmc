/*******************************************************************\

Module: Invariant Propagation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Invariant Propagation

#include "invariant_propagation.h"

#include <util/simplify_expr.h>
#include <util/std_expr.h>

/// Pass the necessary arguments to the invariant_set_domaint's when constructed
class invariant_set_domain_factoryt
  : public ai_domain_factoryt<invariant_set_domaint>
{
public:
  explicit invariant_set_domain_factoryt(invariant_propagationt &_ip) : ip(_ip)
  {
  }

  std::unique_ptr<statet> make(locationt l) const override
  {
    auto p = util_make_unique<invariant_set_domaint>(
      ip.value_sets, ip.object_store, ip.ns);
    CHECK_RETURN(p->is_bottom());

    return std::unique_ptr<statet>(p.release());
  }

private:
  invariant_propagationt &ip;
};

invariant_propagationt::invariant_propagationt(
  const namespacet &_ns,
  value_setst &_value_sets)
  : ait<invariant_set_domaint>(
      util_make_unique<invariant_set_domain_factoryt>(*this)),
    ns(_ns),
    value_sets(_value_sets),
    object_store(_ns)
{
}

void invariant_propagationt::make_all_true()
{
  for(auto &state :
      static_cast<location_sensitive_storaget &>(*storage).internal())
    static_cast<invariant_set_domaint &>(*(state.second))
      .invariant_set.make_true();
}

void invariant_propagationt::make_all_false()
{
  for(auto &state :
      static_cast<location_sensitive_storaget &>(*storage).internal())
    static_cast<invariant_set_domaint &>(*(state.second))
      .invariant_set.make_false();
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

  for(const auto &gf_entry : goto_functions.function_map)
  {
    // get the locals
    std::set<irep_idt> locals;
    get_local_identifiers(gf_entry.second, locals);

    const goto_programt &goto_program = gf_entry.second.body;

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
  else if(type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv)
    return true;
  else if(type.id()==ID_bool)
    return true;

  return false;
}

void invariant_propagationt::initialize(
  const irep_idt &function,
  const goto_programt &goto_program)
{
  baset::initialize(function, goto_program);

  add_objects(goto_program);
}

void invariant_propagationt::simplify(goto_functionst &goto_functions)
{
  for(auto &gf_entry : goto_functions.function_map)
    simplify(gf_entry.second.body);
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

    exprt simplified_guard(i_it->condition());

    invariant_set.simplify(simplified_guard);
    ::simplify(simplified_guard, ns);

    if(invariant_set.implies(simplified_guard).is_true())
      i_it->condition_nonconst() = true_exprt();
  }
}
