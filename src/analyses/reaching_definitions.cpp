/*******************************************************************\

Module: Range-based reaching definitions analysis (following Field-
        Sensitive Program Dependence Analysis, Litvak et al., FSE 2010)

Author: Michael Tautschnig

Date: February 2013

\*******************************************************************/

template <bool remove_locals>
void rd_range_domain_baset<remove_locals>::transform(
  locationt from,
  locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  PRECONDITION(bv_container);

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
  PRECONDITION(range_start >= 0);

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
void rd_range_domain_baset<remove_locals>::kill(
  const irep_idt &identifier,
  const range_spect &range_start,
  const range_spect &range_end)
{
  PRECONDITION(range_start >= 0);
  // -1 for objects of infinite/unknown size
  if(range_end == -1)
  {
    kill_inf(identifier, range_start);
    return;
  }

  PRECONDITION(range_end > range_start);

  values_innert &current_values = get_values_inner(identifier);
  values_innert new_values;

  for(typename values_innert::iterator it = current_values.begin();
      it != current_values.end();) // no ++it
  {
    const reaching_definitiont &v = bv_container->get(*it);

    if(v.bit_begin >= range_end)
      ++it;
    else if(v.bit_end != -1 && v.bit_end <= range_start)
      ++it;
    else if(
      v.bit_begin >= range_start && v.bit_end != -1 &&
      v.bit_end <= range_end) // rs <= a < b <= re
    {
      current_values.erase(it++);
    }
    else if(v.bit_begin >= range_start) // rs <= a <= re < b
    {
      reaching_definitiont v_new = v;
      v_new.bit_begin = range_end;
      new_values.insert(bv_container->add(v_new));

      current_values.erase(it++);
    }
    else if(v.bit_end == -1 || v.bit_end > range_end) // a <= rs < re < b
    {
      reaching_definitiont v_new = v;
      v_new.bit_end = range_start;

      reaching_definitiont v_new2 = v;
      v_new2.bit_begin = range_end;

      new_values.insert(bv_container->add(v_new));
      new_values.insert(bv_container->add(v_new2));

      current_values.erase(it++);
    }
    else // a <= rs < b <= re
    {
      reaching_definitiont v_new = v;
      v_new.bit_end = range_start;
      new_values.insert(bv_container->add(v_new));

      current_values.erase(it++);
    }
  }

  current_values.insert(new_values.begin(), new_values.end());
}

template <bool remove_locals>
void rd_range_domain_baset<remove_locals>::output(
  const irep_idt &identifier,
  std::ostream &out) const
{
  const ranges_at_loct &ranges = get(identifier);

  out << "  " << identifier << "[";

  for(typename ranges_at_loct::const_iterator itl = ranges.begin();
      itl != ranges.end();
      ++itl)
    for(typename rangest::const_iterator itr = itl->second.begin();
        itr != itl->second.end();
        ++itr)
    {
      if(itr != itl->second.begin() || itl != ranges.begin())
        out << ";";

      out << itr->first << ":" << itr->second;
      out << "@" << itl->first->location_number;
    }

  out << "]\n";

  clear_cache(identifier);
}
