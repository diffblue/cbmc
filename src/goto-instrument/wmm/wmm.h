/*******************************************************************\

Module: memory models

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

/// \file
/// memory models

#ifndef CPROVER_GOTO_INSTRUMENT_WMM_WMM_H
#define CPROVER_GOTO_INSTRUMENT_WMM_WMM_H

enum memory_modelt
{
  Unknown=-1,
  TSO=0,
  PSO=1,
  RMO=2,
  Power=3
};

enum instrumentation_strategyt
{
  all=0,
  min_interference=1,
  read_first=2,
  write_first=3,
  my_events=4,
  one_event_per_cycle=5
};

enum loop_strategyt
{
  arrays_only=0,
  all_loops=1,
  no_loop=2
};

#endif // CPROVER_GOTO_INSTRUMENT_WMM_WMM_H
