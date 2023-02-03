/*******************************************************************\

Module: Value Set Propagation (flow insensitive)

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Value Set Propagation (flow insensitive)

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_FI_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_FI_H

#include <analyses/flow_insensitive_analysis.h>

#include "value_set_domain_fi.h"
#include "value_sets.h"

class symbolt;

class value_set_analysis_fit:
  public value_setst,
  public flow_insensitive_analysist<value_set_domain_fit>
{
public:
  enum track_optionst { TRACK_ALL_POINTERS, TRACK_FUNCTION_POINTERS };

  // constructor
  value_set_analysis_fit(
    const namespacet &_ns,
    track_optionst _track_options=TRACK_ALL_POINTERS):
      flow_insensitive_analysist<value_set_domain_fit>(_ns),
      track_options(_track_options)
  {
  }

  typedef flow_insensitive_analysist<value_set_domain_fit> baset;

  void initialize(const goto_programt &goto_program) override;
  void initialize(const goto_functionst &goto_functions) override;

protected:
  track_optionst track_options;

  bool check_type(const typet &type);
  void get_globals(std::list<value_set_fit::entryt> &dest);
  void add_vars(const goto_functionst &goto_functions);
  void add_vars(const goto_programt &goto_programa);

  void get_entries(
    const symbolt &symbol,
    std::list<value_set_fit::entryt> &dest);

  void get_entries_rec(
    const irep_idt &identifier,
    const std::string &suffix,
    const typet &type,
    std::list<value_set_fit::entryt> &dest);

public:
  // interface value_sets
  std::vector<exprt> get_values(
    const irep_idt &function_id,
    locationt l,
    const exprt &expr) override;
};

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_FI_H
