/*******************************************************************\

Module: Range-based reaching definitions analysis (following Field-
        Sensitive Program Dependence Analysis, Litvak et al., FSE 2010)

Author: Michael Tautschnig

Date: February 2013

\*******************************************************************/

/// \file
/// Range-based reaching definitions analysis (following Field- Sensitive
///   Program Dependence Analysis, Litvak et al., FSE 2010)

#ifndef CPROVER_ANALYSES_REACHING_DEFINITIONS_H
#define CPROVER_ANALYSES_REACHING_DEFINITIONS_H

#include <util/base_exceptions.h>
#include <util/invariant.h>
#include <util/make_unique.h>
#include <util/pointer_offset_size.h>
#include <util/prefix.h>
#include <util/threeval.h>

#include <pointer-analysis/value_set_analysis_fi.h>

#include <analyses/ai.h>
#include <analyses/dirty.h>
#include <analyses/goto_rw.h>
#include <analyses/is_threaded.h>

#include <memory>

class value_setst;
class is_threadedt;
class dirtyt;

// requirement: V has a member "identifier" of type irep_idt
template<typename V>
class sparse_bitvector_analysist
{
public:
  const V &get(const std::size_t value_index) const
  {
    PRECONDITION(value_index < values.size());
    return values[value_index]->first;
  }

  std::size_t add(const V &value)
  {
    inner_mapt &m=value_map[value.identifier];

    std::pair<typename inner_mapt::iterator, bool> entry=
      m.insert(std::make_pair(value, values.size()));

    if(entry.second)
      values.push_back(entry.first);

    return entry.first->second;
  }

  void clear()
  {
    value_map.clear();
    values.clear();
  }

protected:
  typedef typename std::map<V, std::size_t> inner_mapt;
  std::vector<typename inner_mapt::const_iterator> values;
  std::unordered_map<irep_idt, inner_mapt> value_map;
};

struct reaching_definitiont
{
  irep_idt identifier;
  ai_domain_baset::locationt definition_at;
  range_spect bit_begin;
  range_spect bit_end;
};

inline bool operator<(
  const reaching_definitiont &a,
  const reaching_definitiont &b)
{
  if(a.definition_at<b.definition_at)
    return true;
  if(b.definition_at<a.definition_at)
    return false;

  if(a.bit_begin<b.bit_begin)
    return true;
  if(b.bit_begin<a.bit_begin)
    return false;

  if(a.bit_end<b.bit_end)
    return true;
  if(b.bit_end<a.bit_end)
    return false;

  INVARIANT(
    a.identifier == b.identifier,
    "No comparison of unrelated definitions"
    "as operator< is only used in sparse_bitvector_analysist");

  return false;
}

namespace
{
struct infot
{
  infot(value_setst &value_sets, is_threadedt &is_threaded, dirtyt &is_dirty)
    : value_sets(value_sets), is_threaded(is_threaded), is_dirty(is_dirty)
  {
  }

  value_setst &value_sets;
  is_threadedt &is_threaded;
  dirtyt &is_dirty;
};

typedef std::set<std::size_t> values_innert;
std::set<std::size_t> values_inner_empty;
}

template <bool remove_locals>
class rd_range_domain_baset : public ai_domain_baset
{
protected:
  rd_range_domain_baset()
    : ai_domain_baset(), has_values(false), bv_container(nullptr)
  {
  }

public:
  void set_bitvector_container(
    sparse_bitvector_analysist<reaching_definitiont> &_bv_container)
  {
    bv_container=&_bv_container;
  }

  void
  transform(locationt from, locationt to, ai_baset &ai, const namespacet &ns)
    final override;

  void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const final override
  {
    output(out);
  }

  // each element x represents a range of bits [x.first, x.second)
  typedef std::multimap<range_spect, range_spect> rangest;
  typedef std::map<locationt, rangest> ranges_at_loct;

  virtual const ranges_at_loct &get(const irep_idt &identifier) const = 0;
  void clear_cache(const irep_idt &identifier) const
  {
    export_cache.erase(identifier);
  }

protected:
  tvt has_values;

  sparse_bitvector_analysist<reaching_definitiont> *bv_container;

  typedef std::set<std::size_t> values_innert;
  #ifdef USE_DSTRING
  typedef std::map<irep_idt, values_innert> valuest;
  #else
  typedef std::unordered_map<irep_idt, values_innert> valuest;
  #endif
  valuest values;

  #ifdef USE_DSTRING
  typedef std::map<irep_idt, ranges_at_loct> export_cachet;
  #else
  typedef std::unordered_map<irep_idt, ranges_at_loct> export_cachet;
  #endif
  mutable export_cachet export_cache;

  virtual infot get_info(ai_baset &ai) = 0;

  virtual void transform_dead(const namespacet &ns, locationt from) = 0;

  virtual void transform_start_thread(const namespacet &ns, ai_baset &ai) = 0;

  virtual void transform_function_call(
    const namespacet &ns,
    locationt from,
    locationt to,
    ai_baset &ai) = 0;

  virtual void transform_end_function(
    const namespacet &ns,
    locationt from,
    locationt to,
    ai_baset &ai) = 0;

  void transform_assign(
    const namespacet &ns,
    locationt from,
    locationt to,
    ai_baset &ai);

  void kill(
    const irep_idt &identifier,
    const range_spect &range_start,
    const range_spect &range_end);

  void kill_inf(
    const irep_idt &identifier,
    const range_spect &range_start);

  virtual bool gen(
    locationt from,
    const irep_idt &identifier,
    const range_spect &range_start,
    const range_spect &range_end) = 0;

  virtual void output(std::ostream &out) const = 0;

  void output(const irep_idt &identifier, std::ostream &out) const;

  virtual values_innert &get_values_inner(const irep_idt &identifier) = 0;
};

template <typename rd_range_domain>
class reaching_definitions_analysis_ait
  : public concurrency_aware_ait<rd_range_domain>,
    public sparse_bitvector_analysist<reaching_definitiont>
{
public:
  using typename concurrency_aware_ait<rd_range_domain>::statet;

  explicit reaching_definitions_analysis_ait(const namespacet &ns) : ns(ns)
  {
  }
  virtual ~reaching_definitions_analysis_ait() = default;

  virtual void initialize(const goto_functionst &goto_functions) override
  {
    auto value_sets_ = util_make_unique<value_set_analysis_fit>(ns);
    (*value_sets_)(goto_functions);
    value_sets = std::move(value_sets_);

    is_threaded = util_make_unique<is_threadedt>(goto_functions);
    is_dirty = util_make_unique<dirtyt>(goto_functions);

    concurrency_aware_ait<rd_range_domain>::initialize(goto_functions);
  }

  virtual statet &get_state(goto_programt::const_targett l) override
  {
    statet &s = concurrency_aware_ait<rd_range_domain>::get_state(l);

    rd_range_domain *rd_state = dynamic_cast<rd_range_domain *>(&s);
    INVARIANT_STRUCTURED(
      rd_state != nullptr,
      bad_cast_exceptiont,
      "rd_state has type rd_range_domain");

    rd_state->set_bitvector_container(*this);

    return s;
  }

  std::unique_ptr<value_setst> value_sets;
  std::unique_ptr<is_threadedt> is_threaded;
  std::unique_ptr<dirtyt> is_dirty;

protected:
  const namespacet &ns;
};

#include "reaching_definitions.cpp"

#endif // CPROVER_ANALYSES_REACHING_DEFINITIONS_H
