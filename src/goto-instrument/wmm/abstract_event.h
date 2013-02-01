/*******************************************************************\

Module: abstract events

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

#ifndef ABSTRACT_EVENT_H
#define ABSTRACT_EVENT_H

#include <location.h>
#include <graph.h>

#include "wmm.h"

/*******************************************************************\
                          abstract event
\*******************************************************************/

class abstract_eventt:public graph_nodet<empty_nodet>
{
protected:
  bool unsafe_pair_lwfence_param(const abstract_eventt& next,
    weak_memory_modelt model, bool lwsync_met) const;

public:
  /* for now, both fence functions and asm fences accepted */
  typedef enum {Write, Read, Fence, Lwfence, ASMfence} operationt;

  operationt operation;
  unsigned thread;
  irep_idt variable;
  unsigned id;
  locationt location;
  bool local;

  // for ASMfence
  bool WRfence;
  bool WWfence;
  bool RRfence;
  bool RWfence;
  bool WWcumul;
  bool RWcumul;
  bool RRcumul;

  abstract_eventt()
  {
  }

  abstract_eventt(
    operationt _op, unsigned _th, irep_idt _var,
    unsigned _id, locationt _loc, bool _local)
    :operation(_op), thread(_th), variable(_var), id(_id),
    location(_loc), local(_local)
  {
  }

  abstract_eventt(operationt _op, unsigned _th, irep_idt _var,
    unsigned _id, locationt _loc, bool _local,
    bool WRf, bool WWf, bool RRf, bool RWf, bool WWc, bool RWc, bool RRc)
    :operation(_op), thread(_th), variable(_var), id(_id),
      location(_loc), local(_local), WRfence(RWf), WWfence(WWf), RRfence(RRf),
      RWfence(WRf), WWcumul(WWc), RWcumul(RWc), RRcumul(RRc)
  {
  }

  /* post declaration (through graph) -- doesn't copy */
  void operator()(const abstract_eventt& other)
  {
    operation=other.operation;
    thread=other.thread;
    variable=other.variable;
    id=other.id;
    location=other.location;
    local=other.local;
  }

  inline bool operator==(const abstract_eventt& other) const
  {
    return (id == other.id);
  }

  inline bool operator<(const abstract_eventt& other) const
  {
    return (id < other.id);
  }

  inline bool is_fence() const {
    return operation==Fence || operation==Lwfence || operation==ASMfence;}

  friend std::ostream& operator<<(std::ostream& s, const abstract_eventt& e)
  {
    return s << e.get_operation() << e.variable;
  }

  /* checks the safety of the pair locally (i.e., w/o taking fences
     or dependencies into account -- use is_unsafe on the whole
     critical cycle for this) */
  bool unsafe_pair(const abstract_eventt& next, weak_memory_modelt model) const
  {
    return unsafe_pair_lwfence_param(next,model,false);
  }

  bool unsafe_pair_lwfence(const abstract_eventt& next,
    weak_memory_modelt model) const
  {
    return unsafe_pair_lwfence_param(next,model,true);
  }

  bool unsafe_pair_asm(const abstract_eventt& next, weak_memory_modelt model,
    unsigned char met) const;

  std::string get_operation() const
  {
    switch(operation)
    {
      case Write: return "W";
      case Read: return "R";
      case Fence: return "F";
      case Lwfence: return "f";
      case ASMfence: return "asm:";
    }
    assert(false);
    return "?";
  }

  bool is_corresponding_fence(const abstract_eventt& first,
    const abstract_eventt& second) const
  {
    return (WRfence && first.operation==Write && second.operation==Read)
      || ((WWfence||WWcumul) && first.operation==Write
         && second.operation==Write)
      || ((RWfence||RWcumul) && first.operation==Read
         && second.operation==Write)
      || ((RRfence||RRcumul) && first.operation==Read
         && second.operation==Read);
  }

  bool is_direct() const { return WWfence || WRfence || RRfence || RWfence; }
  bool is_cumul() const { return WWcumul || RWcumul || RRcumul; }

  unsigned char fence_value() const
  {
    unsigned char value = WRfence + 2*WWfence + 4*RRfence + 8*RWfence
      + 16*WWcumul + 32*RWcumul + 64*RRcumul;
    return value;
  }
};
#endif

