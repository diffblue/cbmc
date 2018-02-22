/*******************************************************************\

Module: Range-based reaching definitions analysis (following Field-
        Sensitive Program Dependence Analysis, Litvak et al., FSE 2010)

Author: Michael Tautschnig

Date: February 2013

\*******************************************************************/

/// \file
/// Range-based reaching definitions analysis (following Field- Sensitive
///   Program Dependence Analysis, Litvak et al., FSE 2010)

#ifndef CPROVER_ANALYSES_REACHING_DEFINITIONS_WITH_SHARING_H
#define CPROVER_ANALYSES_REACHING_DEFINITIONS_WITH_SHARING_H

#include <util/base_exceptions.h>
#include <util/make_unique.h>
#include <util/pointer_offset_size.h>
#include <util/prefix.h>
#include <util/sharing_map.h>
#include <util/threeval.h>

#include <pointer-analysis/value_set_analysis_fi.h>

#include <analyses/ai.h>
#include <analyses/dirty.h>
#include <analyses/goto_rw.h>
#include <analyses/is_threaded.h>

#include <memory>

#include "reaching_definitions.h"

class value_setst;
class is_threadedt;
class dirtyt;

template <bool remove_locals = false>
class rd_range_domain_with_sharingt
  : public rd_range_domain_baset<remove_locals>
{
public:
  using typename rd_range_domain_baset<remove_locals>::locationt;
  using rd_range_domain_baset<remove_locals>::has_values;
  using rd_range_domain_baset<remove_locals>::bv_container;
  using typename rd_range_domain_baset<remove_locals>::ranges_at_loct;
  using typename rd_range_domain_baset<remove_locals>::rangest;
  using rd_range_domain_baset<remove_locals>::export_cache;

  using rd_range_domain_baset<remove_locals>::transform_assign;
  using rd_range_domain_baset<remove_locals>::kill;
  using rd_range_domain_baset<remove_locals>::kill_inf;
  using rd_range_domain_baset<remove_locals>::get;
  using rd_range_domain_baset<remove_locals>::clear_cache;
  using rd_range_domain_baset<remove_locals>::output;

  void make_top() final override
  {
    values.clear();
    has_values = tvt(true);
  }

  void make_bottom() final override
  {
    values.clear();
    has_values = tvt(false);
  }

  void make_entry() final override
  {
    values.clear();
    has_values = tvt::unknown();
  }

  bool is_top() const override final
  {
    DATA_INVARIANT(
      !has_values.is_true() || values.empty(),
      "If domain is top, the value map must be empty");
    return has_values.is_true();
  }

  bool is_bottom() const override final
  {
    DATA_INVARIANT(
      !has_values.is_false() || values.empty(),
      "If domain is bottom, the value map must be empty");
    return has_values.is_false();
  }

  // returns true iff there is something new
  bool merge(
    const rd_range_domain_with_sharingt &other,
    locationt from,
    locationt to);

  bool merge_shared(
    const rd_range_domain_with_sharingt &other,
    locationt from,
    locationt to,
    const namespacet &ns);

private:
  typedef sharing_mapt<irep_idt, values_innert, irep_id_hash> valuest;
  valuest values;

  infot get_info(ai_baset &ai);

  void populate_cache(const irep_idt &identifier) const;

  void transform_dead(const namespacet &ns, locationt from);

  void transform_start_thread(const namespacet &ns, ai_baset &ai);

  void transform_function_call(
    const namespacet &ns,
    locationt from,
    locationt to,
    ai_baset &ai);

  void transform_end_function(
    const namespacet &ns,
    locationt from,
    locationt to,
    ai_baset &ai);

  bool gen(
    locationt from,
    const irep_idt &identifier,
    const range_spect &range_start,
    const range_spect &range_end);

  void output(std::ostream &out) const;

  values_innert &get_values_inner(const irep_idt &identifier);
};

typedef reaching_definitions_analysis_ait<rd_range_domain_with_sharingt<false>>
  reaching_definitions_with_sharing_analysist;

#include "reaching_definitions_with_sharing.cpp"

#endif // CPROVER_ANALYSES_REACHING_DEFINITIONS_WITH_SHARING_H
