/*******************************************************************\

Module: abstract events

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

#include "abstract_event.h"

//#define DEBUG
//#define ASMFENCE

#ifdef DEBUG
#define DEBUG_MESSAGE(a) std::cout<<a<<std::endl
#else
#define DEBUG_MESSAGE(a)
#endif

/*******************************************************************\

Function: abstract_eventt::unsafe_pair_lwfence_param

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool abstract_eventt::unsafe_pair_lwfence_param(const abstract_eventt& next, 
  memory_modelt model,
  bool lwsync_met) const
{
  /* pairs with fences are not properly pairs */
  if(operation==Fence || next.operation==Fence
    || operation==Lwfence || next.operation==Lwfence
    || operation==ASMfence || next.operation==ASMfence)
    return false;

  /* pairs of shared variables */
  if(local || next.local)
    return false;

  switch(model)
  {
  case TSO:
    return (thread==next.thread && operation==Write && next.operation==Read);

  case PSO:
    return (thread==next.thread && operation==Write
      /* lwsyncWW -> mfenceWW */
      && !(operation==Write && next.operation==Write && lwsync_met));

  case RMO:
    return (thread==next.thread
      /* lwsyncWW -> mfenceWW */
      && !(operation==Write && next.operation==Write && lwsync_met)
      /* lwsyncRW -> mfenceRW */
      && !(operation==Read && next.operation==Write && lwsync_met)
      /* lwsyncRR -> mfenceRR */
      && !(operation==Read && next.operation==Read && lwsync_met)
      /* if posWW, wsi maintained by the processor */
      && !(variable==next.variable && operation==Write && next.operation==Write)
      /* if posRW, fri maintained by the processor */
      && !(variable==next.variable && operation==Read && next.operation==Write));

  case Power:
    return ((thread==next.thread
      /* lwsyncWW -> mfenceWW */
      && !(operation==Write && next.operation==Write && lwsync_met)
      /* lwsyncRW -> mfenceRW */
      && !(operation==Read && next.operation==Write && lwsync_met)
      /* lwsyncRR -> mfenceRR */
      && !(operation==Read && next.operation==Read && lwsync_met)
      /* if posWW, wsi maintained by the processor */
      && (variable!=next.variable || operation!=Write || next.operation!=Write))
      /* rfe */
      || (thread!=next.thread && operation==Write && next.operation==Read
        && variable==next.variable));

  case Unknown:;
  }
  assert(false);
  /* unknown memory model */
  return true;
}

/*******************************************************************\

Function: abstract_eventt::unsafe_pair_asm

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool abstract_eventt::unsafe_pair_asm(const abstract_eventt& next,
  memory_modelt model,
  unsigned char met) const
{
  /* pairs with fences are not properly pairs */
  if(operation==Fence || next.operation==Fence
    || operation==Lwfence || next.operation==Lwfence
    || operation==ASMfence || next.operation==ASMfence)
    return false;

  /* pairs of shared variables */
  if(local || next.local)
    return false;

  switch(model)
  {
  case TSO:
    return (thread==next.thread && operation==Write && next.operation==Read 
      && (met&1)==0);
  case PSO:
    return (thread==next.thread && operation==Write
      && (met&3)==0);
  case RMO:
    return (thread==next.thread
      && (met&15)==0
      /* if posWW, wsi maintained by the processor */
      && !(variable==next.variable && operation==Write && next.operation==Write)
      /* if posRW, fri maintained by the processor */
      && !(variable==next.variable && operation==Read && next.operation==Write));
  case Power:
    return ((thread==next.thread
      && (met&15)==0
      /* if posWW, wsi maintained by the processor */
      && (variable!=next.variable || operation!=Write || next.operation!=Write))
      /* rfe */
      || (thread!=next.thread && operation==Write && next.operation==Read
        && variable==next.variable));

  case Unknown:;
  }
  assert(false);
  /* unknown memory model */
  return true;
}

