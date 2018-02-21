
template <bool remove_locals>
void rd_range_domain_baset<remove_locals>::transform(
  locationt from,
  locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  assert(bv_container);

  // kill values
  if(from->is_dead())
    transform_dead(ns, from);
  // kill thread-local values
  else if(from->is_start_thread())
    transform_start_thread(ns, ai);
  // do argument-to-parameter assignments
  else if(from->is_function_call())
    transform_function_call(ns, from, to, ai);
  // cleanup parameters
  else if(from->is_end_function())
    transform_end_function(ns, from, to, ai);
  // lhs assignments
  else if(from->is_assign())
    transform_assign(ns, from, from, ai);
  // initial (non-deterministic) value
  else if(from->is_decl())
    transform_assign(ns, from, from, ai);

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

template <bool remove_locals>
void rd_range_domain_baset<remove_locals>::transform_assign(
  const namespacet &ns,
  locationt from,
  locationt to,
  ai_baset &ai)
{
  infot info = get_info(ai);

  rw_range_set_value_sett rw_set(ns, info.value_sets);
  goto_rw(to, rw_set);
  const bool is_must_alias=rw_set.get_w_set().size()==1;

  forall_rw_range_set_w_objects(it, rw_set)
  {
    const irep_idt &identifier=it->first;
    // ignore symex::invalid_object
    const symbolt *symbol_ptr;
    if(ns.lookup(identifier, symbol_ptr))
      continue;
    INVARIANT_STRUCTURED(
      symbol_ptr!=nullptr,
      nullptr_exceptiont,
      "Symbol is in symbol table");

    const range_domaint &ranges=rw_set.get_ranges(it);

    if(
      is_must_alias &&
      (!info.is_threaded(from) ||
       (!symbol_ptr->is_shared() && !info.is_dirty(identifier))))
      for(const auto &range : ranges)
        kill(identifier, range.first, range.second);

    for(const auto &range : ranges)
      gen(from, identifier, range.first, range.second);
  }
}

template <bool remove_locals>
void rd_range_domain_baset<remove_locals>::kill_inf(
  const irep_idt &identifier,
  const range_spect &range_start)
{
  assert(range_start>=0);

#if 0
  valuest::iterator entry=values.find(identifier);
  if(entry==values.end())
    return;

  bool export_cache_available=false;

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

template <bool remove_locals>
const typename rd_range_domain_baset<remove_locals>::ranges_at_loct &
rd_range_domain_baset<remove_locals>::get(const irep_idt &identifier) const
{
  populate_cache(identifier);

  static ranges_at_loct empty;

  export_cachet::const_iterator entry=export_cache.find(identifier);

  if(entry==export_cache.end())
    return empty;
  else
    return entry->second;
}
