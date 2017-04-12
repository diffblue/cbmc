/*******************************************************************\

Module: Range-based reaching definitions analysis (following Field-
        Sensitive Program Dependence Analysis, Litvak et al., FSE 2010)

Author: Michael Tautschnig

Date: February 2013

\*******************************************************************/

#include <util/pointer_offset_size.h>
#include <util/prefix.h>
#include "util/make_unique.h"

#include <pointer-analysis/value_set_analysis_fi.h>

#include "is_threaded.h"
#include "dirty.h"

#include "reaching_definitions.h"

reaching_definitions_analysist::reaching_definitions_analysist(
  const namespacet &_ns):
    concurrency_aware_ait<rd_range_domaint>(),
    ns(_ns)
{
}


reaching_definitions_analysist::~reaching_definitions_analysist()=default;

/*******************************************************************\

Function: rd_range_domaint::populate_cache

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::populate_cache(const irep_idt &identifier) const
{
  assert(bv_container);

  valuest::const_iterator v_entry=values.find(identifier);
  if(v_entry==values.end() ||
     v_entry->second.empty())
    return;

  ranges_at_loct &export_entry=export_cache[identifier];

  for(const auto &id : v_entry->second)
  {
    const reaching_definitiont &v=bv_container->get(id);

    export_entry[v.definition_at].insert(
      std::make_pair(v.bit_begin, v.bit_end));
  }
}

/*******************************************************************\

Function: rd_range_domaint::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::transform(
  locationt from,
  locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  reaching_definitions_analysist *rd=
    dynamic_cast<reaching_definitions_analysist*>(&ai);
  assert(rd!=0);

  assert(bv_container);

  // kill values
  if(from->is_dead())
    transform_dead(ns, from);
  // kill thread-local values
  else if(from->is_start_thread())
    transform_start_thread(ns, *rd);
  // do argument-to-parameter assignments
  else if(from->is_function_call())
    transform_function_call(ns, from, to, *rd);
  // cleanup parameters
  else if(from->is_end_function())
    transform_end_function(ns, from, to, *rd);
  // lhs assignements
  else if(from->is_assign())
    transform_assign(ns, from, from, *rd);
  // initial (non-deterministic) value
  else if(from->is_decl())
    transform_assign(ns, from, from, *rd);

#if 0
  // handle return values
  if(to->is_function_call())
  {
    const code_function_callt &code=to_code_function_call(to->code);

    if(code.lhs().is_not_nil())
    {
      rw_range_set_value_sett rw_set(ns, rd->get_value_sets());
      goto_rw(to, rw_set);
      const bool is_must_alias=rw_set.get_w_set().size()==1;

      forall_rw_range_set_w_objects(it, rw_set)
      {
        const irep_idt &identifier=it->first;
        // ignore symex::invalid_object
        const symbolt *symbol_ptr;
        if(ns.lookup(identifier, symbol_ptr))
          continue;
        assert(symbol_ptr!=0);

        const range_domaint &ranges=rw_set.get_ranges(it);

        if(is_must_alias &&
           (!rd->get_is_threaded()(from) ||
            (!symbol_ptr->is_shared() &&
             !rd->get_is_dirty()(identifier))))
          for(const auto &range : ranges)
            kill(identifier, range.first, range.second);
      }
    }
  }
#endif
}

/*******************************************************************\

Function: rd_range_domaint::transform_dead

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::transform_dead(
  const namespacet &ns,
  locationt from)
{
  const irep_idt &identifier=
    to_symbol_expr(to_code_dead(from->code).symbol()).get_identifier();

  valuest::iterator entry=values.find(identifier);

  if(entry!=values.end())
  {
    values.erase(entry);
    export_cache.erase(identifier);
  }
}

/*******************************************************************\

Function: rd_range_domaint::transform_start_thread

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::transform_start_thread(
  const namespacet &ns,
  reaching_definitions_analysist &rd)
{
  for(valuest::iterator it=values.begin();
      it!=values.end();
      ) // no ++it
  {
    const irep_idt &identifier=it->first;

    if(!ns.lookup(identifier).is_shared() &&
       !rd.get_is_dirty()(identifier))
    {
      export_cache.erase(identifier);

      valuest::iterator next=it;
      ++next;
      values.erase(it);
      it=next;
    }
    else
      ++it;
  }
}

/*******************************************************************\

Function: rd_range_domaint::transform_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::transform_function_call(
  const namespacet &ns,
  locationt from,
  locationt to,
  reaching_definitions_analysist &rd)
{
  const code_function_callt &code=to_code_function_call(from->code);

  goto_programt::const_targett next=from;
  ++next;

  // only if there is an actual call, i.e., we have a body
  if(next!=to)
  {
    for(valuest::iterator it=values.begin();
        it!=values.end();
       ) // no ++it
    {
      const irep_idt &identifier=it->first;

      // dereferencing may introduce extra symbols
      const symbolt *sym;
      if((ns.lookup(identifier, sym) ||
          !sym->is_shared()) &&
         !rd.get_is_dirty()(identifier))
      {
        export_cache.erase(identifier);

        valuest::iterator next=it;
        ++next;
        values.erase(it);
        it=next;
      }
      else
        ++it;
    }

    const symbol_exprt &fn_symbol_expr=to_symbol_expr(code.function());
    const code_typet &code_type=
      to_code_type(ns.lookup(fn_symbol_expr.get_identifier()).type);

    for(const auto &param : code_type.parameters())
    {
      const irep_idt &identifier=param.get_identifier();

      if(identifier.empty())
        continue;

      range_spect size=
        to_range_spect(pointer_offset_bits(param.type(), ns));
      gen(from, identifier, 0, size);
    }
  }
  else
  {
    // handle return values of undefined functions
    const code_function_callt &code=to_code_function_call(from->code);

    if(code.lhs().is_not_nil())
      transform_assign(ns, from, from, rd);
  }
}

/*******************************************************************\

Function: rd_range_domaint::transform_end_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::transform_end_function(
  const namespacet &ns,
  locationt from,
  locationt to,
  reaching_definitions_analysist &rd)
{
  goto_programt::const_targett call=to;
  --call;
  const code_function_callt &code=to_code_function_call(call->code);

  valuest new_values;
  new_values.swap(values);
  values=rd[call].values;

  for(const auto &new_value : new_values)
  {
    const irep_idt &identifier=new_value.first;

    if(!rd.get_is_threaded()(call) ||
       (!ns.lookup(identifier).is_shared() &&
        !rd.get_is_dirty()(identifier)))
    {
      for(const auto &id : new_value.second)
      {
        const reaching_definitiont &v=bv_container->get(id);
        kill(v.identifier, v.bit_begin, v.bit_end);
      }
    }

    for(const auto &id : new_value.second)
    {
      const reaching_definitiont &v=bv_container->get(id);
      gen(v.definition_at, v.identifier, v.bit_begin, v.bit_end);
    }
  }

  const code_typet &code_type=
    to_code_type(ns.lookup(from->function).type);

  for(const auto &param : code_type.parameters())
  {
    const irep_idt &identifier=param.get_identifier();

    if(identifier.empty())
      continue;

    valuest::iterator entry=values.find(identifier);

    if(entry!=values.end())
    {
      values.erase(entry);
      export_cache.erase(identifier);
    }
  }

  // handle return values
  if(code.lhs().is_not_nil())
  {
#if 0
    rd_range_domaint *rd_state=
      dynamic_cast<rd_range_domaint*>(&(rd.get_state(call)));
    assert(rd_state!=0);
    rd_state->
#endif
      transform_assign(ns, from, call, rd);
  }
}

/*******************************************************************\

Function: rd_range_domaint::transform_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::transform_assign(
  const namespacet &ns,
  locationt from,
  locationt to,
  reaching_definitions_analysist &rd)
{
  rw_range_set_value_sett rw_set(ns, rd.get_value_sets());
  goto_rw(to, rw_set);
  const bool is_must_alias=rw_set.get_w_set().size()==1;

  forall_rw_range_set_w_objects(it, rw_set)
  {
    const irep_idt &identifier=it->first;
    // ignore symex::invalid_object
    const symbolt *symbol_ptr;
    if(ns.lookup(identifier, symbol_ptr))
      continue;
    assert(symbol_ptr!=0);

    const range_domaint &ranges=rw_set.get_ranges(it);

    if(is_must_alias &&
       (!rd.get_is_threaded()(from) ||
        (!symbol_ptr->is_shared() &&
         !rd.get_is_dirty()(identifier))))
      for(const auto &range : ranges)
        kill(identifier, range.first, range.second);

    for(const auto &range : ranges)
      gen(from, identifier, range.first, range.second);
  }
}

/*******************************************************************\

Function: rd_range_domaint::kill

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::kill(
  const irep_idt &identifier,
  const range_spect &range_start,
  const range_spect &range_end)
{
  assert(range_start>=0);
  // -1 for objects of infinite/unknown size
  if(range_end==-1)
  {
    kill_inf(identifier, range_start);
    return;
  }

  assert(range_end>range_start);

  valuest::iterator entry=values.find(identifier);
  if(entry==values.end())
    return;

  bool clear_export_cache=false;
  values_innert new_values;

  for(values_innert::iterator
      it=entry->second.begin();
      it!=entry->second.end();
     ) // no ++it
  {
    const reaching_definitiont &v=bv_container->get(*it);

    if(v.bit_begin >= range_end)
      ++it;
    else if(v.bit_end!=-1 &&
            v.bit_end <= range_start)
      ++it;
    else if(v.bit_begin >= range_start &&
            v.bit_end!=-1 &&
            v.bit_end <= range_end) // rs <= a < b <= re
    {
      clear_export_cache=true;

      entry->second.erase(it++);
    }
    else if(v.bit_begin >= range_start) // rs <= a <= re < b
    {
      clear_export_cache=true;

      reaching_definitiont v_new=v;
      v_new.bit_begin=range_end;
      new_values.insert(bv_container->add(v_new));

      entry->second.erase(it++);
    }
    else if(v.bit_end==-1 ||
            v.bit_end > range_end) // a <= rs < re < b
    {
      clear_export_cache=true;

      reaching_definitiont v_new=v;
      v_new.bit_end=range_start;

      reaching_definitiont v_new2=v;
      v_new2.bit_begin=range_end;

      new_values.insert(bv_container->add(v_new));
      new_values.insert(bv_container->add(v_new2));

      entry->second.erase(it++);
    }
    else // a <= rs < b <= re
    {
      clear_export_cache=true;

      reaching_definitiont v_new=v;
      v_new.bit_end=range_start;
      new_values.insert(bv_container->add(v_new));

      entry->second.erase(it++);
    }
  }

  if(clear_export_cache)
    export_cache.erase(identifier);

  values_innert::iterator it=entry->second.begin();
  for(const auto &id : new_values)
  {
    while(it!=entry->second.end() && *it<id)
      ++it;
    if(it==entry->second.end() || id<*it)
    {
      entry->second.insert(it, id);
    }
    else if(it!=entry->second.end())
    {
      assert(*it==id);
      ++it;
    }
  }
}

/*******************************************************************\

Function: rd_range_domaint::kill_inf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::kill_inf(
  const irep_idt &identifier,
  const range_spect &range_start)
{
  assert(range_start>=0);

#if 0
  valuest::iterator entry=values.find(identifier);
  if(entry==values.end())
    return;

  XXX export_cache_available=false;

  // makes the analysis underapproximating
  rangest &ranges=entry->second;

  for(rangest::iterator it=ranges.begin();
      it!=ranges.end();
     ) // no ++it
    if(it->second.first!=-1 &&
       it->second.first <= range_start)
      ++it;
    else if(it->first >= range_start) // rs <= a < b <= re
    {
      ranges.erase(it++);
    }
    else // a <= rs < b < re
    {
      it->second.first=range_start;
      ++it;
    }
#endif
}

/*******************************************************************\

Function: rd_range_domaint::gen

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool rd_range_domaint::gen(
  locationt from,
  const irep_idt &identifier,
  const range_spect &range_start,
  const range_spect &range_end)
{
  // objects of size 0 like union U { signed : 0; };
  if(range_start==0 && range_end==0)
    return false;

  assert(range_start>=0);

  // -1 for objects of infinite/unknown size
  assert(range_end>range_start || range_end==-1);

  reaching_definitiont v;
  v.identifier=identifier;
  v.definition_at=from;
  v.bit_begin=range_start;
  v.bit_end=range_end;

  if(!values[identifier].insert(bv_container->add(v)).second)
    return false;

  export_cache.erase(identifier);

#if 0
  range_spect merged_range_end=range_end;

  std::pair<valuest::iterator, bool> entry=
    values.insert(std::make_pair(identifier, rangest()));
  rangest &ranges=entry.first->second;

  if(!entry.second)
  {
    for(rangest::iterator it=ranges.begin();
        it!=ranges.end();
        ) // no ++it
    {
      if(it->second.second!=from ||
         (it->second.first!=-1 && it->second.first <= range_start) ||
         (range_end!=-1 && it->first >= range_end))
        ++it;
      else if(it->first > range_start) // rs < a < b,re
      {
        if(range_end!=-1)
          merged_range_end=std::max(range_end, it->second.first);
        ranges.erase(it++);
      }
      else if(it->second.first==-1 ||
              (range_end!=-1 &&
               it->second.first >= range_end)) // a <= rs < re <= b
      {
        // nothing to do
        return false;
      }
      else // a <= rs < b < re
      {
        it->second.first=range_end;
        return true;
      }
    }
  }

  ranges.insert(std::make_pair(
      range_start,
      std::make_pair(merged_range_end, from)));
#endif

  return true;
}

/*******************************************************************\

Function: rd_range_domaint::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::output(std::ostream &out) const
{
  out << "Reaching definitions:" << std::endl;

  if(has_values.is_known())
  {
    out << has_values.to_string() << '\n';
    return;
  }

  for(const auto &value : values)
  {
    const irep_idt &identifier=value.first;

    const ranges_at_loct &ranges=get(identifier);

    out << "  " << identifier << "[";

    for(ranges_at_loct::const_iterator itl=ranges.begin();
        itl!=ranges.end();
        ++itl)
      for(rangest::const_iterator itr=itl->second.begin();
          itr!=itl->second.end();
          ++itr)
      {
        if(itr!=itl->second.begin() ||
           itl!=ranges.begin())
          out << ";";

        out << itr->first << ":" << itr->second;
        out << "@" << itl->first->location_number;
      }

    out << "]" << std::endl;

    clear_cache(identifier);
  }
}

/*******************************************************************\

Function: rd_range_domaint::merge_inner

  Inputs:

 Outputs: returns true iff there is s.th. new

 Purpose:

\*******************************************************************/

bool rd_range_domaint::merge_inner(
  values_innert &dest,
  const values_innert &other)
{
  bool more=false;

#if 0
  ranges_at_loct::iterator itr=it->second.begin();
  for(const auto &o : ito->second)
  {
    while(itr!=it->second.end() && itr->first<o.first)
      ++itr;
    if(itr==it->second.end() || o.first<itr->first)
    {
      it->second.insert(o);
      more=true;
    }
    else if(itr!=it->second.end())
    {
      assert(itr->first==o.first);

      for(const auto &o_range : o.second)
        more=gen(itr->second, o_range.first, o_range.second) ||
          more;

      ++itr;
    }
  }
#else
  values_innert::iterator itr=dest.begin();
  for(const auto &id : other)
  {
    while(itr!=dest.end() && *itr<id)
      ++itr;
    if(itr==dest.end() || id<*itr)
    {
      dest.insert(itr, id);
      more=true;
    }
    else if(itr!=dest.end())
    {
      assert(*itr==id);
      ++itr;
    }
  }
#endif

  return more;
}

/*******************************************************************\

Function: rd_range_domaint::merge

  Inputs:

 Outputs: returns true iff there is s.th. new

 Purpose:

\*******************************************************************/

bool rd_range_domaint::merge(
  const rd_range_domaint &other,
  locationt from,
  locationt to)
{
  bool changed=has_values.is_false();
  has_values=tvt::unknown();

  valuest::iterator it=values.begin();
  for(const auto &value : other.values)
  {
    while(it!=values.end() && it->first<value.first)
      ++it;
    if(it==values.end() || value.first<it->first)
    {
      values.insert(value);
      changed=true;
    }
    else if(it!=values.end())
    {
      assert(it->first==value.first);

      if(merge_inner(it->second, value.second))
      {
        changed=true;
        export_cache.erase(it->first);
      }

      ++it;
    }
  }

  return changed;
}

/*******************************************************************\

Function: rd_range_domaint::merge_shared

  Inputs:

 Outputs: returns true iff there is s.th. new

 Purpose:

\*******************************************************************/

bool rd_range_domaint::merge_shared(
  const rd_range_domaint &other,
  goto_programt::const_targett from,
  goto_programt::const_targett to,
  const namespacet &ns)
{
  // TODO: dirty vars
#if 0
  reaching_definitions_analysist *rd=
    dynamic_cast<reaching_definitions_analysist*>(&ai);
  assert(rd!=0);
#endif

  bool changed=has_values.is_false();
  has_values=tvt::unknown();

  valuest::iterator it=values.begin();
  for(const auto &value : other.values)
  {
    const irep_idt &identifier=value.first;

    if(!ns.lookup(identifier).is_shared()
       /*&& !rd.get_is_dirty()(identifier)*/)
      continue;

    while(it!=values.end() && it->first<value.first)
      ++it;
    if(it==values.end() || value.first<it->first)
    {
      values.insert(value);
      changed=true;
    }
    else if(it!=values.end())
    {
      assert(it->first==value.first);

      if(merge_inner(it->second, value.second))
      {
        changed=true;
        export_cache.erase(it->first);
      }

      ++it;
    }
  }

  return changed;
}

/*******************************************************************\

Function: rd_range_domaint::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const rd_range_domaint::ranges_at_loct &rd_range_domaint::get(
  const irep_idt &identifier) const
{
  populate_cache(identifier);

  static ranges_at_loct empty;

  export_cachet::const_iterator entry=export_cache.find(identifier);

  if(entry==export_cache.end())
    return empty;
  else
    return entry->second;
}

/*******************************************************************\

Function: reaching_definitions_analysist::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void reaching_definitions_analysist::initialize(
  const goto_functionst &goto_functions)
{
  auto value_sets_=util_make_unique<value_set_analysis_fit>(ns);
  (*value_sets_)(goto_functions);
  value_sets=std::move(value_sets_);

  is_threaded=util_make_unique<is_threadedt>(goto_functions);

  is_dirty=util_make_unique<dirtyt>(goto_functions);

  concurrency_aware_ait<rd_range_domaint>::initialize(goto_functions);
}
