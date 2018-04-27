/*******************************************************************\

Module: Value Set Propagation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Value Set Propagation

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_H

#include "value_set_domain.h"
#include "value_sets.h"

#include <analyses/ai.h>

class xmlt;

void value_sets_to_xml(
  std::function<const value_sett &(goto_programt::const_targett)> get_value_set,
  const goto_programt &goto_program,
  const irep_idt &identifier,
  xmlt &dest);

template<class VSDT>
class value_set_analysis_templatet:
  public ait<VSDT>,
  public value_setst
{
public:
  typedef VSDT domaint;
  typedef ait<domaint> baset;
  typedef typename baset::locationt locationt;

  void convert(
    const goto_programt &goto_program,
    const irep_idt &identifier,
    xmlt &dest) const
  {
    value_sets_to_xml(
      [this](locationt l) { return (*this)[l].value_set; },
      goto_program,
      identifier,
      dest);
  }

  virtual void initialize(const goto_programt &goto_program) override
  {
    baset::initialize(goto_program);
    forall_goto_program_instructions(i_it, goto_program)
    {
      static_cast<domaint &>(this->get_state(i_it)).value_set.location_number =
        i_it->location_number;
    }
  }

  void analyze_all_functions(const goto_modelt &goto_model)
  {
    // Unlike operator(), which starts at __CPROVER_start and only analyses
    // reachable code, assume all functions are externally reachable.
    namespacet ns(goto_model.symbol_table);

    baset::initialize(goto_model.goto_functions);

    forall_goto_functions(it, goto_model.goto_functions)
    {
      if(it->second.body.instructions.empty())
        continue;
      const auto &start_state =
        static_cast<const domaint &>(
          this->find_state(it->second.body.instructions.begin()));
      if(start_state.is_bottom())
      {
        this->entry_state(it->second.body);
        ai_baset::fixedpoint(it->second.body, goto_model.goto_functions, ns);
      }
    }

    this->finalize();
  }

public:
  // interface value_sets
  virtual void get_values(
    locationt l,
    const exprt &expr,
    value_setst::valuest &dest,
    const namespacet &ns) override
  {
    (*this)[l].value_set.get_value_set(expr, dest, ns);
  }
};

typedef
  value_set_analysis_templatet<value_set_domain_templatet<value_sett>>
  value_set_analysist;

void convert(
  const goto_functionst &goto_functions,
  const value_set_analysist &value_set_analysis,
  xmlt &dest);

void convert(
  const goto_programt &goto_program,
  const value_set_analysist &value_set_analysis,
  xmlt &dest);

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_H
