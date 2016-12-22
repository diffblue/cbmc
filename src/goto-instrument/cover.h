/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

Date: May 2016

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_COVER_H
#define CPROVER_GOTO_INSTRUMENT_COVER_H

#include "cover_utils.h"

class instrument_cover_goalst : public instrument_cover_utilst
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
    goto_programt::instructionst::iterator &insn);

  void instrument_cover(
    goto_programt::instructionst::iterator &insn);

  void instrument_location(
    goto_programt::instructionst::iterator &insn,
    goto_programt &goto_program,
    basic_blockst &basic_blocks,
    std::set<unsigned> &blocks_done);

  void instrument_branch(
    goto_programt::instructionst::iterator &insn,
    goto_programt &goto_program,
    basic_blockst &basic_blocks);

  void instrument_condition(
    goto_programt::instructionst::iterator &insn,
    goto_programt &goto_program);

  void instrument_decision(
    goto_programt::instructionst::iterator &insn,
    goto_programt &goto_program);

  const namespacet ns;
  const std::set<coverage_criteriont> &criteria;
  irep_idt coverage_criterion;
  irep_idt property_class;
};

#endif // CPROVER_GOTO_INSTRUMENT_COVER_H
