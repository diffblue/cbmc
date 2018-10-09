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
#include <util/threeval.h>

#include "ai.h"
#include "goto_rw.h"

class value_setst;
class is_threadedt;
class dirtyt;
class reaching_definitions_analysist;

// requirement: V has a member "identifier" of type irep_idt
template<typename V>
class sparse_bitvector_analysist
{
public:
  const V &get(const std::size_t value_index) const
  {
    assert(value_index<values.size());
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

  // we do not expect comparison of unrelated definitions
  // as this operator< is only used in sparse_bitvector_analysist
  assert(a.identifier==b.identifier);

  return false;
}

class rd_range_domaint:public ai_domain_baset
{
public:
  rd_range_domaint():
    ai_domain_baset(),
    has_values(false),
    bv_container(nullptr)
  {
  }

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
    const ai_baset &,
    const namespacet &) const final override
  {
    output(out);
  }

  void make_top() final override
  {
    values.clear();
    if(bv_container)
      bv_container->clear();
    has_values=tvt(true);
  }

  void make_bottom() final override
  {
    values.clear();
    if(bv_container)
      bv_container->clear();
    has_values=tvt(false);
  }

  void make_entry() final override
  {
    make_top();
  }

  bool is_top() const override final
  {
    DATA_INVARIANT(!has_values.is_true() || values.empty(),
                   "If domain is top, the value map must be empty");
    return has_values.is_true();
  }

  bool is_bottom() const override final
  {
    DATA_INVARIANT(!has_values.is_false() || values.empty(),
                   "If domain is bottom, the value map must be empty");
    return has_values.is_false();
  }

  // returns true iff there is something new
  bool merge(
    const rd_range_domaint &other,
    locationt from,
    locationt to);

  bool merge_shared(
    const rd_range_domaint &other,
    locationt from,
    locationt to,
    const namespacet &ns);

  // each element x represents a range of bits [x.first, x.second)
  typedef std::multimap<range_spect, range_spect> rangest;
  typedef std::map<locationt, rangest> ranges_at_loct;

  const ranges_at_loct &get(const irep_idt &identifier) const;
  void clear_cache(const irep_idt &identifier) const
  {
    export_cache[identifier].clear();
  }

private:
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

  void populate_cache(const irep_idt &identifier) const;

  void transform_dead(
    const namespacet &ns,
    locationt from);
  void transform_start_thread(
    const namespacet &ns,
    reaching_definitions_analysist &rd);
  void transform_function_call(
    const namespacet &ns,
    locationt from,
    locationt to,
    reaching_definitions_analysist &rd);
  void transform_end_function(
    const namespacet &ns,
    locationt from,
    locationt to,
    reaching_definitions_analysist &rd);
  void transform_assign(
    const namespacet &ns,
    locationt from,
    locationt to,
    reaching_definitions_analysist &rd);

  void kill(
    const irep_idt &identifier,
    const range_spect &range_start,
    const range_spect &range_end);
  void kill_inf(
    const irep_idt &identifier,
    const range_spect &range_start);
  bool gen(
    locationt from,
    const irep_idt &identifier,
    const range_spect &range_start,
    const range_spect &range_end);

  void output(std::ostream &out) const;

  bool merge_inner(
    values_innert &dest,
    const values_innert &other);
};

class reaching_definitions_analysist:
  public concurrency_aware_ait<rd_range_domaint>,
  public sparse_bitvector_analysist<reaching_definitiont>
{
public:
  // constructor
  explicit reaching_definitions_analysist(const namespacet &_ns);

  virtual ~reaching_definitions_analysist();

  virtual void initialize(
    const goto_functionst &goto_functions) override;

  virtual statet &get_state(locationt l) override
  {
    statet &s=concurrency_aware_ait<rd_range_domaint>::get_state(l);

    rd_range_domaint *rd_state=dynamic_cast<rd_range_domaint*>(&s);
    INVARIANT_STRUCTURED(
      rd_state!=nullptr,
      bad_cast_exceptiont,
      "rd_state has type rd_range_domaint");

    rd_state->set_bitvector_container(*this);

    return s;
  }

  value_setst &get_value_sets() const
  {
    assert(value_sets);
    return *value_sets;
  }

  const is_threadedt &get_is_threaded() const
  {
    assert(is_threaded);
    return *is_threaded;
  }

  const dirtyt &get_is_dirty() const
  {
    assert(is_dirty);
    return *is_dirty;
  }

protected:
  const namespacet &ns;
  std::unique_ptr<value_setst> value_sets;
  std::unique_ptr<is_threadedt> is_threaded;
  std::unique_ptr<dirtyt> is_dirty;
};

#endif // CPROVER_ANALYSES_REACHING_DEFINITIONS_H
