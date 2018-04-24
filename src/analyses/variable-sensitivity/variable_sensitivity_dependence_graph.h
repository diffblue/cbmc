/*******************************************************************\

 Module: analyses variable-sensitivity variable-sensitivity-dependence-graph

 Author: Diffblue Ltd.

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_DEPENDENCE_GRAPH_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_DEPENDENCE_GRAPH_H

#include "variable_sensitivity_domain.h"

#include <ostream>

class variable_sensitivity_dependence_grapht:
  public variable_sensitivity_domaint
{
public:

  void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) override;

  virtual bool merge(
    const variable_sensitivity_domaint &b,
    locationt from,
    locationt to) override;

  virtual void merge_three_way_function_return(
    const ai_domain_baset &function_call,
    const ai_domain_baset &function_start,
    const ai_domain_baset &function_end,
    const namespacet &ns) override;


  void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const override;

  jsont output_json(
    const ai_baset &ai,
    const namespacet &ns) const override;

private:
  class dependency_ordert
  {
  public:
    bool operator()(
      const goto_programt::const_targett &a,
      const goto_programt::const_targett &b) const
    {
      return a->location_number < b->location_number;
    }
  };
  typedef std::set<goto_programt::const_targett, dependency_ordert> data_depst;
  data_depst domain_data_deps;

  void eval_data_deps(
    const exprt &expr, const namespacet &ns, data_depst &deps) const;
};

// NOLINTNEXTLINE(whitespace/line_length)
#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_DEPENDENCE_GRAPH_H
