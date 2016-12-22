/*******************************************************************\

Module: MCDC Instrumentation

Author: Daniel Kroening

Date: May 2016

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_COVER_MCDC_H
#define CPROVER_GOTO_INSTRUMENT_COVER_MCDC_H

#include "cover_utils.h"

class instrument_mcdc_goalst: public instrument_cover_utilst
{
public:
  instrument_mcdc_goalst(
    const namespacet &_ns,
    const std::set<coverage_criteriont> &_criteria,
    const irep_idt &_coverage_criterion,
    const irep_idt &_property_class):
    ns(_ns),
    criteria(_criteria),
    coverage_criterion(_coverage_criterion),
    property_class(_property_class)
    {
    }

  void instrument_mcdc(
    goto_programt::instructionst::iterator &insn,
    goto_programt &goto_program,
    basic_blockst &basic_blocks,
    std::set<unsigned> &blocks_done);

private:
  const namespacet ns;
  const std::set<coverage_criteriont> &criteria;
  const irep_idt coverage_criterion;
  const irep_idt property_class;
};

#endif // CPROVER_GOTO_INSTRUMENT_COVER_MCDC_H
