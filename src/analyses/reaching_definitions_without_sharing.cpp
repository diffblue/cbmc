/*******************************************************************\

Module: Range-based reaching definitions analysis (following Field-
        Sensitive Program Dependence Analysis, Litvak et al., FSE 2010)

Author: Michael Tautschnig

Date: February 2013

\*******************************************************************/

template <bool remove_locals>
infot rd_range_domain_without_sharingt<remove_locals>::get_info(ai_baset &ai)
{
  reaching_definitions_analysist *rd =
    dynamic_cast<reaching_definitions_analysist *>(&ai);
  INVARIANT_STRUCTURED(
    rd != nullptr,
    bad_cast_exceptiont,
    "ai has type reaching_definitions_analysist");

  return infot(*rd->value_sets, *rd->is_threaded, *rd->is_dirty);
}

template <bool remove_locals>
const typename rd_range_domain_without_sharingt<remove_locals>::ranges_at_loct &
rd_range_domain_without_sharingt<remove_locals>::get(
  const irep_idt &identifier) const
{
  PRECONDITION(bv_container);

  static ranges_at_loct empty;

  // Return cached value
  auto e_it = export_cache.find(identifier);
  if(e_it != export_cache.end())
    return e_it->second;

  // Check if values available
  auto v_it = values.find(identifier);
  if(v_it == values.end() || v_it->second.empty())
    return empty;

  ranges_at_loct &entry = export_cache[identifier];

  for(const auto &id : v_it->second)
  {
    const reaching_definitiont &v = bv_container->get(id);

    entry[v.definition_at].insert(std::make_pair(v.bit_begin, v.bit_end));
  }

  return entry;
}

template <bool remove_locals>
void rd_range_domain_without_sharingt<remove_locals>::transform_dead(
  const namespacet &ns,
  locationt from)
{
  const irep_idt &identifier =
    to_symbol_expr(to_code_dead(from->code).symbol()).get_identifier();

  typename valuest::iterator entry = values.find(identifier);

  if(entry != values.end())
  {
    values.erase(entry);
  }
}

template <bool remove_locals>
void rd_range_domain_without_sharingt<remove_locals>::transform_start_thread(
  const namespacet &ns,
  ai_baset &ai)
{
  infot info = get_info(ai);

  for(typename valuest::iterator it = values.begin();
      it != values.end();) // no ++it
  {
    const irep_idt &identifier = it->first;

    if(!ns.lookup(identifier).is_shared() && !info.is_dirty(identifier))
    {
      typename valuest::iterator next = it;
      ++next;
      values.erase(it);
      it = next;
    }
    else
      ++it;
  }
}

template <bool remove_locals>
void rd_range_domain_without_sharingt<remove_locals>::transform_function_call(
  const namespacet &ns,
  locationt from,
  locationt to,
  ai_baset &ai)
{
  infot info = get_info(ai);

  const code_function_callt &code = to_code_function_call(from->code);

  // only if there is an actual call, i.e., we have a body
  if(from->function != to->function)
  {
    for(typename valuest::iterator it = values.begin();
        it != values.end();) // no ++it
    {
      const irep_idt &identifier = it->first;

      // dereferencing may introduce extra symbols
      const symbolt *sym;
      if(
        (ns.lookup(identifier, sym) || !sym->is_shared()) &&
        !info.is_dirty(identifier))
      {
        typename valuest::iterator next = it;
        ++next;
        values.erase(it);
        it = next;
      }
      else
        ++it;
    }

    const symbol_exprt &fn_symbol_expr = to_symbol_expr(code.function());
    const code_typet &code_type =
      to_code_type(ns.lookup(fn_symbol_expr.get_identifier()).type);

    for(const auto &param : code_type.parameters())
    {
      const irep_idt &identifier = param.get_identifier();

      if(identifier.empty())
        continue;

      range_spect size = to_range_spect(pointer_offset_bits(param.type(), ns));
      gen(from, identifier, 0, size);
    }
  }
  else
  {
    // handle return values of undefined functions
    const code_function_callt &code = to_code_function_call(from->code);

    if(code.lhs().is_not_nil())
      transform_assign(ns, from, from, ai);
  }
}

template <bool remove_locals>
void rd_range_domain_without_sharingt<remove_locals>::transform_end_function(
  const namespacet &ns,
  locationt from,
  locationt to,
  ai_baset &ai)
{
  goto_programt::const_targett call = to;
  --call;
  const code_function_callt &code = to_code_function_call(call->code);

  reaching_definitions_analysist *p =
    dynamic_cast<reaching_definitions_analysist *>(&ai);
  INVARIANT_STRUCTURED(
    p != nullptr,
    bad_cast_exceptiont,
    "ai has type reaching_definitions_analysist");
  reaching_definitions_analysist &rd = *p;

  valuest new_values;
  new_values.swap(values);
  values = rd[call].values;

  infot info = get_info(ai);

  for(const auto &new_value : new_values)
  {
    const irep_idt &identifier = new_value.first;

    if(
      !info.is_threaded(call) ||
      (!ns.lookup(identifier).is_shared() && !info.is_dirty(identifier)))
    {
      for(const auto &id : new_value.second)
      {
        const reaching_definitiont &v = bv_container->get(id);
        kill(v.identifier, v.bit_begin, v.bit_end);
      }
    }

    for(const auto &id : new_value.second)
    {
      const reaching_definitiont &v = bv_container->get(id);
      gen(v.definition_at, v.identifier, v.bit_begin, v.bit_end);
    }
  }

  const code_typet &code_type = to_code_type(ns.lookup(from->function).type);

  for(const auto &param : code_type.parameters())
  {
    const irep_idt &identifier = param.get_identifier();

    if(identifier.empty())
      continue;

    typename valuest::iterator entry = values.find(identifier);

    if(entry != values.end())
    {
      values.erase(entry);
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
    transform_assign(ns, from, call, ai);
  }
}

template <bool remove_locals>
bool rd_range_domain_without_sharingt<remove_locals>::gen(
  locationt from,
  const irep_idt &identifier,
  const range_spect &range_start,
  const range_spect &range_end)
{
  // objects of size 0 like union U { signed : 0; };
  if(range_start == 0 && range_end == 0)
    return false;

  PRECONDITION(range_start >= 0);

  // -1 for objects of infinite/unknown size
  PRECONDITION(range_end > range_start || range_end == -1);

  reaching_definitiont v;
  v.identifier = identifier;
  v.definition_at = from;
  v.bit_begin = range_start;
  v.bit_end = range_end;

  if(!values[identifier].insert(bv_container->add(v)).second)
    return false;

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

template <bool remove_locals>
void rd_range_domain_without_sharingt<remove_locals>::output(
  std::ostream &out) const
{
  out << "Reaching definitions:\n";

  if(has_values.is_known())
  {
    out << has_values.to_string() << '\n';
    return;
  }

  for(const auto &value : values)
  {
    const irep_idt &identifier = value.first;
    output(identifier, out);
  }
}

template <bool remove_locals>
values_innert &
rd_range_domain_without_sharingt<remove_locals>::get_values_inner(
  const irep_idt &identifier)
{
  typename valuest::iterator entry = values.find(identifier);
  if(entry == values.end())
    return values_inner_empty;

  return entry->second;
}

/// \return returns true iff there is something new
template <bool remove_locals>
bool rd_range_domain_without_sharingt<remove_locals>::merge_inner(
  values_innert &dest,
  const values_innert &other)
{
  bool more = false;

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
  typename values_innert::iterator itr = dest.begin();
  for(const auto &id : other)
  {
    while(itr != dest.end() && *itr < id)
      ++itr;
    if(itr == dest.end() || id < *itr)
    {
      dest.insert(itr, id);
      more = true;
    }
    else if(itr != dest.end())
    {
      INVARIANT(*itr == id, "!= handled by other cases");
      ++itr;
    }
  }
#endif

  return more;
}

/// \return returns true iff there is something new
template <bool remove_locals>
bool rd_range_domain_without_sharingt<remove_locals>::merge(
  const rd_range_domain_without_sharingt &other,
  locationt from,
  locationt to)
{
  bool changed = has_values.is_false();
  has_values = tvt::unknown();

  typename valuest::iterator it = values.begin();
  for(const auto &value : other.values)
  {
    while(it != values.end() && it->first < value.first)
      ++it;
    if(it == values.end() || value.first < it->first)
    {
      values.insert(value);
      changed = true;
    }
    else if(it != values.end())
    {
      INVARIANT(it->first == value.first, "!= handled by other cases");

      if(merge_inner(it->second, value.second))
      {
        changed = true;
      }

      ++it;
    }
  }

  return changed;
}

/// \return returns true iff there is something new
template <bool remove_locals>
bool rd_range_domain_without_sharingt<remove_locals>::merge_shared(
  const rd_range_domain_without_sharingt &other,
  locationt from,
  locationt to,
  const namespacet &ns)
{
// TODO: dirty vars
#if 0
  reaching_definitions_analysist *rd=
    dynamic_cast<reaching_definitions_analysist*>(&ai);
  assert(rd!=0);
#endif

  bool changed = has_values.is_false();
  has_values = tvt::unknown();

  typename valuest::iterator it = values.begin();
  for(const auto &value : other.values)
  {
    const irep_idt &identifier = value.first;

    if(
      !ns.lookup(identifier).is_shared()
      /*&& !rd.get_is_dirty()(identifier)*/)
      continue;

    while(it != values.end() && it->first < value.first)
      ++it;
    if(it == values.end() || value.first < it->first)
    {
      values.insert(value);
      changed = true;
    }
    else if(it != values.end())
    {
      INVARIANT(it->first == value.first, "!= handled by other cases");

      if(merge_inner(it->second, value.second))
      {
        changed = true;
      }

      ++it;
    }
  }

  return changed;
}
