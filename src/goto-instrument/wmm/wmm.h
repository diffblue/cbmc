/*******************************************************************\

Module: memory models

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

#ifndef MEMORY_MODEL
#define MEMORY_MODEL

typedef enum {
  Unknown=-1,
  TSO=0, 
  PSO=1, 
  RMO=2, 
  Power=3
} memory_modelt;

#endif

#ifndef INSTRUMENTATION_STRATEGY
#define INSTRUMENTATION_STRATEGY

typedef enum {
  all=0,
  min_interference=1,
  read_first=2,
  write_first=3,
  my_events=4,
  one_event_per_cycle
} instrumentation_strategyt;

#endif
