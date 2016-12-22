/*******************************************************************\

Module: Coverage Instrumentation Utils

Author: Daniel Kroening

Date: May 2016

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_COVER_UTILS_H
#define CPROVER_GOTO_INSTRUMENT_COVER_UTILS_H

#include <goto-programs/goto_model.h>

enum class coverage_criteriont
{
  LOCATION, BRANCH, DECISION, CONDITION,
  PATH, MCDC, BOUNDARY, ASSERTION, COVER
};

class basic_blockst
{
public:
  explicit basic_blockst(const goto_programt &_goto_program)
  {
    bool next_is_target=true;
    unsigned block_count=0;

    forall_goto_program_instructions(it, _goto_program)
    {
      if(next_is_target || it->is_target())
        block_count++;

      block_map[it]=block_count;

      if(!it->source_location.is_nil() &&
         source_location_map.find(block_count)==source_location_map.end())
        source_location_map[block_count]=it->source_location;

      next_is_target=
        it->is_goto() || it->is_function_call() || it->is_assume();
    }
  }

  // map program locations to block numbers
  typedef std::map<goto_programt::const_targett, unsigned> block_mapt;
  block_mapt block_map;

  // map block numbers to source code locations
  typedef std::map<unsigned, source_locationt> source_location_mapt;
  source_location_mapt source_location_map;

  inline unsigned operator[](goto_programt::const_targett t)
  {
    return block_map[t];
  }

  void output(std::ostream &out)
  {
    for(block_mapt::const_iterator
        b_it=block_map.begin();
        b_it!=block_map.end();
        b_it++)
      out << b_it->first->source_location
          << " -> " << b_it->second
          << '\n';
  }
};

class instrument_cover_utilst
{
public:
  instrument_cover_utilst()
  {
  }

protected:
  std::set<exprt> collect_conditions(
    const goto_programt::const_targett t);

  static std::set<exprt> non_ordered_expr_expansion(
    const exprt &src);

  std::set<exprt> decision_expansion(
    const exprt &dec);

  void collect_mcdc_controlling_rec(
    const exprt &src,
    const std::vector<exprt> &conditions,
    std::set<exprt> &result);

  std::set<exprt> collect_mcdc_controlling(
    const std::set<exprt> &decisions);

  std::set<exprt> collect_mcdc_controlling_nested(
    const std::set<exprt> &decisions);

  std::set<signed> sign_of_expr(
    const exprt &e,
    const exprt &E);

  void remove_repetition(std::set<exprt> &exprs);

  bool eval_expr(
    const std::map<exprt, signed> &atomic_exprs,
    const exprt &src);

  std::map<exprt, signed> values_of_atomic_exprs(
    const exprt &e,
    const std::set<exprt> &conditions);

  bool is_mcdc_pair(
    const exprt &e1,
    const exprt &e2,
    const exprt &c,
    const std::set<exprt> &conditions,
    const exprt &decision);

  bool has_mcdc_pair(
    const exprt &c,
    const std::set<exprt> &expr_set,
    const std::set<exprt> &conditions,
    const exprt &decision);

  void minimize_mcdc_controlling(
    std::set<exprt> &controlling,
    const exprt &decision);

  void collect_decisions_rec(
    const exprt &src,
    std::set<exprt> &dest);

  std::set<exprt> collect_decisions(
    const goto_programt::const_targett t);

  std::set<exprt> collect_decisions(
    const exprt &src);
};

#endif // CPROVER_GOTO_INSTRUMENT_COVER_UTILS_H
