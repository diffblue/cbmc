/*******************************************************************\

Module: abstract events

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

/// \file
/// abstract events

#include "abstract_event.h"

bool abstract_eventt::unsafe_pair_lwfence_param(const abstract_eventt &next,
  memory_modelt model,
  bool lwsync_met) const
{
  /* pairs with fences are not properly pairs */
  if(operation==operationt::Fence || next.operation==operationt::Fence
    || operation==operationt::Lwfence || next.operation==operationt::Lwfence
    || operation==operationt::ASMfence || next.operation==operationt::ASMfence)
    return false;

  /* pairs of shared variables */
  if(local || next.local)
    return false;

  switch(model)
  {
  case TSO:
    return (thread==next.thread &&
            operation==operationt::Write &&
            next.operation==operationt::Read);

  case PSO:
    return (thread==next.thread && operation==operationt::Write
      /* lwsyncWW -> mfenceWW */
      && !(operation==operationt::Write &&
           next.operation==operationt::Write &&
           lwsync_met));

  case RMO:
    return
      thread==next.thread &&
      /* lwsyncWW -> mfenceWW */
      !(operation==operationt::Write &&
        next.operation==operationt::Write &&
        lwsync_met) &&
      /* lwsyncRW -> mfenceRW */
      !(operation==operationt::Read &&
        next.operation==operationt::Write &&
        lwsync_met) &&
      /* lwsyncRR -> mfenceRR */
      !(operation==operationt::Read &&
        next.operation==operationt::Read &&
        lwsync_met) &&
      /* if posWW, wsi maintained by the processor */
      !(variable==next.variable &&
        operation==operationt::Write &&
        next.operation==operationt::Write) &&
      /* if posRW, fri maintained by the processor */
      !(variable==next.variable &&
        operation==operationt::Read &&
        next.operation==operationt::Write);

  case Power:
    return ((thread==next.thread
      /* lwsyncWW -> mfenceWW */
      && !(operation==operationt::Write &&
           next.operation==operationt::Write &&
           lwsync_met)
      /* lwsyncRW -> mfenceRW */
      && !(operation==operationt::Read &&
           next.operation==operationt::Write &&
           lwsync_met)
      /* lwsyncRR -> mfenceRR */
      && !(operation==operationt::Read &&
           next.operation==operationt::Read &&
           lwsync_met)
      /* if posWW, wsi maintained by the processor */
      && (variable!=next.variable ||
          operation!=operationt::Write ||
          next.operation!=operationt::Write))
      /* rfe */
      || (thread!=next.thread &&
          operation==operationt::Write &&
          next.operation==operationt::Read &&
          variable==next.variable));

  case Unknown:
    {
    }
  }
  assert(false);
  /* unknown memory model */
  return true;
}

bool abstract_eventt::unsafe_pair_asm(const abstract_eventt &next,
  memory_modelt model,
  unsigned char met) const
{
  /* pairs with fences are not properly pairs */
  if(operation==operationt::Fence ||
     next.operation==operationt::Fence ||
     operation==operationt::Lwfence ||
     next.operation==operationt::Lwfence ||
     operation==operationt::ASMfence ||
     next.operation==operationt::ASMfence)
    return false;

  /* pairs of shared variables */
  if(local || next.local)
    return false;

  switch(model)
  {
  case TSO:
    return (thread==next.thread &&
            operation==operationt::Write &&
            next.operation==operationt::Read &&
            (met&1)==0);
  case PSO:
    return (thread==next.thread &&
            operation==operationt::Write &&
            (met&3)==0);
  case RMO:
    return
      thread==next.thread &&
      (met&15)==0 &&
      /* if posWW, wsi maintained by the processor */
      !(variable==next.variable &&
        operation==operationt::Write &&
          next.operation==operationt::Write) &&
      /* if posRW, fri maintained by the processor */
      !(variable==next.variable &&
        operation==operationt::Read &&
        next.operation==operationt::Write);
  case Power:
    return
      (thread==next.thread &&
       (met&15)==0 &&
       /* if posWW, wsi maintained by the processor */
       (variable!=next.variable ||
        operation!=operationt::Write ||
        next.operation!=operationt::Write)) ||
      /* rfe */
      (thread!=next.thread &&
       operation==operationt::Write &&
       next.operation==operationt::Read &&
       variable==next.variable);

  case Unknown:
    {
    }
  }
  assert(false);
  /* unknown memory model */
  return true;
}
