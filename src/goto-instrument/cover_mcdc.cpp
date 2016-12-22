/*******************************************************************\

Module: Coverage Instrumentation for MCDC

Author: Daniel Kroening

Date: May 2016

\*******************************************************************/

#include <algorithm>

#include "cover_mcdc.h"

/*******************************************************************\

Function: instrument_mcdc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_mcdc_goalst::instrument_mcdc(
  goto_programt::instructionst::iterator &insn,
  goto_programt &goto_program,
  basic_blockst &basic_blocks,
  std::set<unsigned> &blocks_done)
{
  if(insn->is_assert())
    insn->make_skip();

  // 1. Each entry and exit point is invoked
  // 2. Each decision takes every possible outcome
  // 3. Each condition in a decision takes every possible outcome
  // 4. Each condition in a decision is shown to independently
  //    affect the outcome of the decision.

  const std::set<exprt> conditions=collect_conditions(insn);

  const std::set<exprt> decisions=collect_decisions(insn);

  std::set<exprt> both;
  std::set_union(conditions.begin(), conditions.end(),
                 decisions.begin(), decisions.end(),
                 inserter(both, both.end()));

  const source_locationt source_location=insn->source_location;

  for(const auto & p : both)
  {
    bool is_decision=decisions.find(p)!=decisions.end();
    bool is_condition=conditions.find(p)!=conditions.end();

    std::string description=
      (is_decision && is_condition)?"decision/condition":
      is_decision?"decision":"condition";

    std::string p_string=from_expr(ns, "", p);

    std::string comment_t=description+" `"+p_string+"' true";
    goto_program.insert_before_swap(insn);
    insn->make_assertion(not_exprt(p));
    insn->source_location=source_location;
    insn->source_location.set_comment(comment_t);
    insn->source_location.set(ID_coverage_criterion, coverage_criterion);
    insn->source_location.set_property_class(property_class);

    std::string comment_f=description+" `"+p_string+"' false";
    goto_program.insert_before_swap(insn);
    insn->make_assertion(p);
    insn->source_location=source_location;
    insn->source_location.set_comment(comment_f);
    insn->source_location.set(ID_coverage_criterion, coverage_criterion);
    insn->source_location.set_property_class(property_class);
  }

  bool boundary_values_analysis=
       criteria.find(coverage_criteriont::BOUNDARY)!=criteria.end();
  std::set<exprt> controlling;
  for(auto &dec : decisions)
  {
    std::set<exprt> ctrl=collect_mcdc_controlling_nested({dec});
    if(boundary_values_analysis)
    {
      auto res=decision_expansion(dec);
      ctrl.insert(res.begin(), res.end());
    }
    remove_repetition(ctrl);
    minimize_mcdc_controlling(ctrl, dec);
    controlling.insert(ctrl.begin(), ctrl.end());
  }

  if(boundary_values_analysis)
  {
    std::set<exprt> boundary_controlling;
    for(auto &x : controlling)
    {
      auto res=non_ordered_expr_expansion(x);
      boundary_controlling.insert(res.begin(), res.end());
    }
    controlling=boundary_controlling;
    remove_repetition(controlling);
  }

  for(const auto & p : controlling)
  {
    std::string p_string=from_expr(ns, "", p);

    std::string description=
      "MC/DC independence condition `"+p_string+"'";

    goto_program.insert_before_swap(insn);
    insn->make_assertion(not_exprt(p));
    insn->source_location=source_location;
    insn->source_location.set_comment(description);
    insn->source_location.set(ID_coverage_criterion, coverage_criterion);
    insn->source_location.set_property_class(property_class);
  }

  for(std::size_t i=0; i<both.size()*2+controlling.size(); i++)
    insn++;
}
