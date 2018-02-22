
template <bool remove_locals>
infot rd_range_domain_with_sharingt<remove_locals>::get_info(ai_baset &ai)
{
  reaching_definitions_with_sharing_analysist *rd =
    dynamic_cast<reaching_definitions_with_sharing_analysist *>(&ai);
  INVARIANT_STRUCTURED(
    rd != nullptr,
    bad_cast_exceptiont,
    "ai has type reaching_definitions_with_sharing_analysist");

  return infot(*rd->value_sets, *rd->is_threaded, *rd->is_dirty);
}

template <bool remove_locals>
void rd_range_domain_with_sharingt<remove_locals>::populate_cache(
  const irep_idt &identifier) const
{
  assert(bv_container);

  auto &r = values.find(identifier);

  if(!r.second)
    return;

  const values_innert &inner = r.first;

  if(inner.empty())
    return;

  ranges_at_loct &export_entry = export_cache[identifier];

  for(const auto &id : inner)
  {
    const reaching_definitiont &v = bv_container->get(id);

    export_entry[v.definition_at].insert(
      std::make_pair(v.bit_begin, v.bit_end));
  }
}

template <bool remove_locals>
void rd_range_domain_with_sharingt<remove_locals>::transform_dead(
  const namespacet &ns,
  locationt from)
{
  const irep_idt &identifier =
    to_symbol_expr(to_code_dead(from->code).symbol()).get_identifier();

  values.erase(identifier);
}

template <bool remove_locals>
void rd_range_domain_with_sharingt<remove_locals>::transform_start_thread(
  const namespacet &ns,
  ai_baset &ai)
{
  throw "transform_start_thread() unimplemented";
}

template <bool remove_locals>
void rd_range_domain_with_sharingt<remove_locals>::transform_function_call(
  const namespacet &ns,
  locationt from,
  locationt to,
  ai_baset &ai)
{
  infot info = get_info(ai);

  const code_function_callt &code = to_code_function_call(from->code);

  goto_programt::const_targett next = from;
  ++next;

  // only if there is an actual call, i.e., we have a body
  if(next != to)
  {
    if(remove_locals)
    {
      typename valuest::viewt view;
      values.get_view(view);

      for(const auto &p : view)
      {
        const irep_idt &identifier = p.first;

        const symbolt *sym;

        if(
          (ns.lookup(identifier, sym) || !sym->is_shared()) &&
          !info.is_dirty(identifier))
        {
          values.erase(identifier);
        }
      }
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
void rd_range_domain_with_sharingt<remove_locals>::transform_end_function(
  const namespacet &ns,
  locationt from,
  locationt to,
  ai_baset &ai)
{
  goto_programt::const_targett call = to;
  --call;
  const code_function_callt &code = to_code_function_call(call->code);

  if(remove_locals)
  {
    reaching_definitions_with_sharing_analysist *p =
      dynamic_cast<reaching_definitions_with_sharing_analysist *>(&ai);
    INVARIANT_STRUCTURED(
      p != nullptr,
      bad_cast_exceptiont,
      "ai has type reaching_definitions_with_sharing_analysist");
    reaching_definitions_with_sharing_analysist &rd = *p;

    valuest new_values;
    new_values.swap(values);
    values = rd[call].values;

    typename valuest::viewt view;
    new_values.get_view(view);

    infot info = get_info(ai);

    for(const auto &new_value : view)
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
  }

  const code_typet &code_type = to_code_type(ns.lookup(from->function).type);

  for(const auto &param : code_type.parameters())
  {
    const irep_idt &identifier = param.get_identifier();

    if(identifier.empty())
      continue;

    values.erase(identifier);
  }

  // handle return values
  if(code.lhs().is_not_nil())
  {
    transform_assign(ns, from, call, ai);
  }
}

template <bool remove_locals>
bool rd_range_domain_with_sharingt<remove_locals>::gen(
  locationt from,
  const irep_idt &identifier,
  const range_spect &range_start,
  const range_spect &range_end)
{
  // objects of size 0 like union U { signed : 0; };
  if(range_start == 0 && range_end == 0)
    return false;

  assert(range_start >= 0);

  // -1 for objects of infinite/unknown size
  assert(range_end > range_start || range_end == -1);

  reaching_definitiont v;
  v.identifier = identifier;
  v.definition_at = from;
  v.bit_begin = range_start;
  v.bit_end = range_end;

  size_t id = bv_container->add(v);

  const auto &r = values[identifier].insert(id);
  if(!r.second)
    return false;

  return true;
}

template <bool remove_locals>
void rd_range_domain_with_sharingt<remove_locals>::output(
  std::ostream &out) const
{
  out << "Reaching definitions:" << std::endl;

  if(has_values.is_known())
  {
    out << has_values.to_string() << '\n';
    return;
  }

  typename valuest::viewt view;
  values.get_view(view);

  for(const auto &value : view)
  {
    const irep_idt &identifier = value.first;
    output(identifier, out);
  }
}

template <bool remove_locals>
values_innert &rd_range_domain_with_sharingt<remove_locals>::get_values_inner(
  const irep_idt &identifier)
{
  auto &r = values.find(identifier);
  if(!r.second)
    return values_inner_empty;

  return r.first;
}

/// \return returns true iff there is something new
template <bool remove_locals>
bool rd_range_domain_with_sharingt<remove_locals>::merge(
  const rd_range_domain_with_sharingt &other,
  locationt from,
  locationt to)
{
  bool changed = false;

  if(other.has_values.is_false())
  {
    assert(other.values.empty());
    return false;
  }

  if(has_values.is_false())
  {
    assert(values.empty());

    values = other.values;

    assert(!other.has_values.is_true());
    has_values = other.has_values;

    return true;
  }

  rd_range_domain_with_sharingt &o =
    const_cast<rd_range_domain_with_sharingt &>(other);
  values.swap(o.values);

  typename valuest::delta_viewt delta_view;
  o.values.get_delta_view(values, delta_view);

  for(const auto &element : delta_view)
  {
    bool in_both = element.in_both;
    const irep_idt &k = element.k;
    const values_innert &inner_other = element.m; // in other
    const values_innert &inner = element.other_m; // in this

    if(!in_both)
    {
      values.insert(k, inner_other);
      changed = true;
    }
    else
    {
      if(inner != inner_other)
      {
        auto &v = values.find(k);
        assert(v.second);

        values_innert &inner = v.first;

        size_t n = inner.size();
        inner.insert(inner_other.begin(), inner_other.end());
        if(inner.size() != n)
          changed = true;
      }
    }
  }

  return changed;
}

/// \return returns true iff there is something new
template <bool remove_locals>
bool rd_range_domain_with_sharingt<remove_locals>::merge_shared(
  const rd_range_domain_with_sharingt &other,
  locationt from,
  locationt to,
  const namespacet &ns)
{
  throw "merge_shared() unimplemented";

  return true;
}
