/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

Date: May 2016

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_COVER_H
#define CPROVER_GOTO_INSTRUMENT_COVER_H

#include <goto-programs/goto_model.h>

enum class coverage_criteriont {
  LOCATION, BRANCH, DECISION, CONDITION,
  PATH, MCDC, BOUNDARY, ASSERTION, COVER};

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

class instrument_cover_goalst
{
public:
  instrument_cover_goalst(
    const symbol_tablet &_symbol_table,
    const std::set<coverage_criteriont> &_criteria):
    ns(_symbol_table),
    criteria(_criteria)
  {
  }

  void instrument_cover_goals(
    goto_programt &goto_program);

  void instrument_cover_goals(
    goto_functionst &goto_functions);

private:

  void instrument_assertion(
    goto_programt::instructionst::iterator &i_it);

  void instrument_cover(
    goto_programt::instructionst::iterator &i_it);

  void instrument_location(
    goto_programt::instructionst::iterator &i_it,
    goto_programt &goto_program,
    basic_blockst &basic_blocks,
    std::set<unsigned> &blocks_done);

  void instrument_branch(
    goto_programt::instructionst::iterator &i_it,
    goto_programt &goto_program,
    basic_blockst &basic_blocks);

  void instrument_condition(
    goto_programt::instructionst::iterator &i_it,
    goto_programt &goto_program);

  void instrument_decision(
    goto_programt::instructionst::iterator &i_it,
    goto_programt &goto_program);

  void instrument_mcdc(
    goto_programt::instructionst::iterator &i_it,
    goto_programt &goto_program,
    basic_blockst &basic_blocks,
    std::set<unsigned> &blocks_done);

  const namespacet ns;
  const std::set<coverage_criteriont> &criteria;
  irep_idt coverage_criterion;
  irep_idt property_class;
};

#endif // CPROVER_GOTO_INSTRUMENT_COVER_H
