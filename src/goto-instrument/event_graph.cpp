/*******************************************************************\

Module: graph of abstract events

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

#include "event_graph.h"
#include <util/i2string.h>

//#define DEBUG

#ifdef DEBUG
#define DEBUG_MESSAGE(a) std::cout<<a<<std::endl
#else
#define DEBUG_MESSAGE(a)
#endif

#define NB_COLOURS 14
std::string colour_map[NB_COLOURS] = {"red", "blue", "black", "green", "yellow",
"orange", "blueviolet", "cyan", "cadetblue", "magenta", "palegreen",
"deeppink", "indigo", "olivedrab"};
#define print_colour(u) colour_map[u%NB_COLOURS]

/*******************************************************************\

Function: abstract_eventt::unsafe_pair_lwfence_param

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool abstract_eventt::unsafe_pair_lwfence_param(const abstract_eventt& next, 
  weak_memory_modelt model,
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

  if(model==TSO)
    return (thread==next.thread && operation==Write && next.operation==Read);
  else if(model==PSO)
    return (thread==next.thread && operation==Write
      /* lwsyncWW -> mfenceWW */
      && !(operation==Write && next.operation==Write && lwsync_met));
  else if(model==RMO)
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
  else if(model==Power)
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
  else
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
  weak_memory_modelt model,
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

  if(model==TSO)
    return (thread==next.thread && operation==Write && next.operation==Read 
      && (met&1)==0);
  else if(model==PSO)
    return (thread==next.thread && operation==Write
      && (met&3)==0);
  else if(model==RMO)
    return (thread==next.thread
      && (met&15)==0
      /* if posWW, wsi maintained by the processor */
      && !(variable==next.variable && operation==Write && next.operation==Write)
      /* if posRW, fri maintained by the processor */
      && !(variable==next.variable && operation==Read && next.operation==Write));
  else if(model==Power)
    return ((thread==next.thread
      && (met&15)==0
      /* if posWW, wsi maintained by the processor */
      && (variable!=next.variable || operation!=Write || next.operation!=Write))
      /* rfe */
      || (thread!=next.thread && operation==Write && next.operation==Read
        && variable==next.variable));
  else
    /* unknown memory model */
    return true;
}


/*******************************************************************\

Function: event_grapht::critical_cyclet::is_unsafe

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool event_grapht::critical_cyclet::is_unsafe(weak_memory_modelt model, bool fast)
{
  DEBUG_MESSAGE("cycle is safe?");
  bool unsafe_met = false;

  /* critical cycles contain at least 4 events */
  if(size()<4)
    return false;

  /* selects the first element of the pair */
  for(const_iterator it=begin(); it!=end() && ++it!=end(); it++)
  {
    --it;

    /* strong fence -- this pair is safe */
    if(egraph[*it].operation==abstract_eventt::Fence)
      continue;

    if(egraph[*(++it)].operation==abstract_eventt::Fence)
    {
      --it;
      continue;
    }

    --it;

    /* first element is a weak fence */
    if(egraph[*it].operation==abstract_eventt::Lwfence)
      continue;

    /* selects the next event which is not a weak fence */
    const_iterator s_it = ++it;
    --it;

    for(; 
      s_it!=end() && egraph[*s_it].operation==abstract_eventt::Lwfence; s_it++);

    if(s_it==end())
      continue;

    if(egraph[*s_it].operation==abstract_eventt::Fence)
      continue;

    /* if the whole cycle has been explored */
    if(it==s_it)
      continue;

    const abstract_eventt& first = egraph[*it];
    const abstract_eventt& second = egraph[*s_it];

    const data_dpt& data_dp = egraph.map_data_dp[first.thread];

    /* if data dp between linking the pair, safe */
    if(first.thread==second.thread && data_dp.dp(first,second))
      continue;

    /* AC and BC conditions */
    if(first.thread!=second.thread && model==Power)
    {
      bool AC = false;
      bool BC = false;

      /* no fence after the second element? (AC) */
      const_iterator AC_it = ++s_it;
      --s_it;
      for(;
        AC_it!=end() && egraph[*AC_it].thread==second.thread;
        AC_it++)
        if(egraph[*AC_it].operation==abstract_eventt::Fence)
        {
          AC = true;
          break;
        }

      if(AC)
        continue;

      if(AC_it==end() && egraph[front()].thread==second.thread)
        for(AC_it=begin();
          !(egraph[*AC_it]==first) && egraph[*AC_it].thread==second.thread;
          AC_it++)
          if(egraph[*AC_it].operation==abstract_eventt::Fence)
          {
            AC = true;
            break;
          }

      if(AC)
        continue;

      /* no fence before the first element? (BC) */
      const_iterator BC_it;
      if(it==begin())
      {
        BC_it = end();
        BC_it--;
      }
      else
      {
        BC_it = --it;
        ++it;
      }
      for(;
        BC_it!=begin() && egraph[*BC_it].thread==first.thread;
        BC_it--)
        if(egraph[*BC_it].operation==abstract_eventt::Fence)
        {
          BC = true;
          break;
        }

      if(BC)
        continue;

      if(BC_it==begin() && egraph[back()].thread==first.thread)
        for(BC_it=end();
          !(egraph[*BC_it]==second) && egraph[*BC_it].thread==first.thread;
          BC_it--)
          if(egraph[*BC_it].operation==abstract_eventt::Fence)
          {
            BC = true;
            break;
          }

      if(BC)
        continue;
    }

    if(s_it==++it)
    {
      --it;

      /* no lwfence between the pair */
      if(first.unsafe_pair(second,model) 
        && (first.thread!=second.thread || egraph.are_po_ordered(*it,*s_it)))
      {
        if(fast)
          return true;
        else
        {
          const delayt delay(*it,*s_it,(first.thread==second.thread));
          unsafe_pairs.insert(delay);
          unsafe_met = true;
        }
      }
    }
    else
    {
      --it;

      /* one (or more) lwfence between the pair */
      if(first.unsafe_pair_lwfence(second,model)
        && (first.thread!=second.thread || egraph.are_po_ordered(*it,*s_it)))
      {
        if(fast)
          return true;
        else
        {
          const delayt delay(*it,*s_it,(first.thread==second.thread));
          unsafe_pairs.insert(delay);
          unsafe_met = true;
        }
      }
    }
  }

  /* strong fence -- this pair is safe */
  if(egraph[back()].operation==abstract_eventt::Fence
    || egraph[front()].operation==abstract_eventt::Fence)
    return unsafe_met;

  /* first element is a weak fence */
  if(egraph[back()].operation==abstract_eventt::Lwfence)
    return unsafe_met;

  /* selects the next event which is not a weak fence */
  const_iterator s_it;
  for(s_it=begin(); 
    s_it!=end() && egraph[*s_it].operation==abstract_eventt::Lwfence; s_it++);

  /* if the whole cycle has been explored */
  if(s_it==end())
    return unsafe_met;

  if(egraph[*s_it].operation==abstract_eventt::Fence)
    return unsafe_met;

  const abstract_eventt& first = egraph[back()];
  const abstract_eventt& second = egraph[*s_it];

  const data_dpt& data_dp = egraph.map_data_dp[first.thread];

  /* if data dp between linking the pair, safe */
  if(first.thread==second.thread && data_dp.dp(first,second))
    return unsafe_met;

  /* AC and BC conditions */
  if(first.thread!=second.thread && model==Power)
  {
    bool AC = false;
    bool BC = false;

    /* no fence after the second element? (AC) */
    const_iterator AC_it = ++s_it;
    --s_it;
    for(;
      AC_it!=end() && egraph[*AC_it].thread==second.thread;
      AC_it++)
      if(egraph[*AC_it].operation==abstract_eventt::Fence)
      {
        AC = true;
        break;
      }

    if(AC)
      return unsafe_met;

    if(AC_it==end() && egraph[front()].thread==second.thread)
      for(AC_it=begin();
        !(egraph[*AC_it]==first) && egraph[*AC_it].thread==second.thread;
        AC_it++)
        if(egraph[*AC_it].operation==abstract_eventt::Fence)
        {
          AC = true;
          break;
        }

    if(AC)
      return unsafe_met;

    /* no fence before the first element? (BC) */
    const_iterator BC_it = end();
    --BC_it;
    
    for(;
      BC_it!=begin() && egraph[*BC_it].thread==first.thread;
      BC_it--)
      if(egraph[*BC_it].operation==abstract_eventt::Fence)
      {
        BC = true;
        break;
      }

    if(BC)
      return unsafe_met;

    if(BC_it==begin() && egraph[back()].thread==first.thread)
    {
      BC_it = end();
      BC_it--;
      for(;
        !(egraph[*BC_it]==second) && egraph[*BC_it].thread==first.thread;
        BC_it--)
        if(egraph[*BC_it].operation==abstract_eventt::Fence)
        {
          BC = true;
          break;
        }
    }

    if(BC)
      return unsafe_met;
  }

  if(s_it==begin())
  {
    /* no lwfence between the pair */
    if(first.unsafe_pair(second,model) 
      && (first.thread!=second.thread || egraph.are_po_ordered(back(),*s_it)))
    {
      if(!fast)
      {
        const delayt delay(back(),*s_it,(first.thread==second.thread));
        unsafe_pairs.insert(delay);
      }
      return true;
    }
  }
  else
  {
    /* one (or more) lwfence between the pair */
    if(first.unsafe_pair_lwfence(second,model)
      && (first.thread!=second.thread || egraph.are_po_ordered(back(),*s_it)))
    {
      if(!fast)
      {
        const delayt delay(back(),*s_it,(first.thread==second.thread));
        unsafe_pairs.insert(delay);
      }
      return true;
    }
  }

  return unsafe_met;
}

/*******************************************************************\

Function: event_grapht::critical_cyclet::is_unsafe

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool event_grapht::critical_cyclet::is_unsafe_asm(weak_memory_modelt model, 
  bool fast)
{
  DEBUG_MESSAGE("cycle is safe?");
  bool unsafe_met = false;
  unsigned char fences_met = 0;

  /* critical cycles contain at least 4 events */
  if(size()<4)
    return false;

  /* selects the first element of the pair */
  for(const_iterator it=begin(); it!=end() && ++it!=end(); it++)
  {
    --it;
    fences_met = 0;

    /* fence -- this pair is safe */
    if(egraph[*it].operation==abstract_eventt::ASMfence)
      continue;

    if(egraph[*(++it)].operation==abstract_eventt::ASMfence)
    {
      --it;
      continue;
    }

    --it;

    /* selects the next event which is not a weak fence */
    const_iterator s_it = ++it;
    --it;

    for(; 
      s_it!=end() && egraph[*s_it].operation==abstract_eventt::ASMfence; 
      s_it++)
      fences_met |= egraph[*s_it].fence_value();

    if(s_it==end())
      continue;

    if(egraph[*s_it].operation==abstract_eventt::ASMfence)
      continue;

    /* if the whole cycle has been explored */
    if(it==s_it)
      continue;

    const abstract_eventt& first = egraph[*it];
    const abstract_eventt& second = egraph[*s_it];

    const data_dpt& data_dp = egraph.map_data_dp[first.thread];

    /* if data dp between linking the pair, safe */
    if(first.thread==second.thread && data_dp.dp(first,second))
      continue;

    /* AC and BC conditions */
    if(first.thread!=second.thread && model==Power)
    {
      bool AC = false;
      bool BC = false;

      /* no fence after the second element? (AC) */
      const_iterator AC_it = ++s_it;
      --s_it;
      for(;
        AC_it!=end() && egraph[*AC_it].thread==second.thread;
        AC_it++)
        if(egraph[*AC_it].operation==abstract_eventt::ASMfence
          && egraph[*AC_it].is_cumul() 
          && egraph[*AC_it].is_corresponding_fence(egraph[*it],egraph[*s_it]))
        {
          AC = true;
          break;
        }

      if(AC)
        continue;

      if(AC_it==end() && egraph[front()].thread==second.thread)
        for(AC_it=begin();
          !(egraph[*AC_it]==first) && egraph[*AC_it].thread==second.thread;
          AC_it++)
          if(egraph[*AC_it].operation==abstract_eventt::ASMfence
            && egraph[*AC_it].is_cumul()
            && egraph[*AC_it].is_corresponding_fence(egraph[*it],egraph[*s_it]))
          {
            AC = true;
            break;
          }

      if(AC)
        continue;

      /* no fence before the first element? (BC) */
      const_iterator BC_it;
      if(it==begin())
      {
        BC_it = end();
        BC_it--;
      }
      else
      {
        BC_it = --it;
        ++it;
      }
      for(;
        BC_it!=begin() && egraph[*BC_it].thread==first.thread;
        BC_it--)
        if(egraph[*BC_it].operation==abstract_eventt::ASMfence
          && egraph[*BC_it].is_cumul()
          && egraph[*BC_it].is_corresponding_fence(egraph[*it],egraph[*s_it]))

        {
          BC = true;
          break;
        }

      if(BC)
        continue;

      if(BC_it==begin() && egraph[back()].thread==first.thread)
        for(BC_it=end();
          !(egraph[*BC_it]==second) && egraph[*BC_it].thread==first.thread;
          BC_it--)
          if(egraph[*BC_it].operation==abstract_eventt::ASMfence
          && egraph[*BC_it].is_cumul()
          && egraph[*BC_it].is_corresponding_fence(egraph[*it],egraph[*s_it]))

          {
            BC = true;
            break;
          }

      if(BC)
        continue;
    }

    if(s_it==++it)
    {
      --it;

      /* no lwfence between the pair */
      if(first.unsafe_pair(second,model) 
        && (first.thread!=second.thread || egraph.are_po_ordered(*it,*s_it)))
      {
        if(fast)
          return true;
        else
        {
          const delayt delay(*it,*s_it,(first.thread==second.thread));
          unsafe_pairs.insert(delay);
          unsafe_met = true;
        }
      }
    }
    else
    {
      --it;

      /* one (or more) lwfence between the pair */
      if(first.unsafe_pair_asm(second, model, fences_met)
        && (first.thread!=second.thread || egraph.are_po_ordered(*it,*s_it)))
      {
        if(fast)
          return true;
        else
        {
          const delayt delay(*it,*s_it,(first.thread==second.thread));
          unsafe_pairs.insert(delay);
          unsafe_met = true;
        }
      }
    }
  }

  /* strong fence -- this pair is safe */
  if(egraph[back()].operation==abstract_eventt::ASMfence
    || egraph[front()].operation==abstract_eventt::ASMfence)
    return unsafe_met;

  fences_met = 0;

  /* selects the next event which is not a weak fence */
  const_iterator s_it;
  for(s_it=begin(); 
    s_it!=end() && egraph[*s_it].operation==abstract_eventt::ASMfence; s_it++)
    fences_met |= egraph[*s_it].fence_value();

  /* if the whole cycle has been explored */
  if(s_it==end())
    return unsafe_met;

  if(egraph[*s_it].operation==abstract_eventt::ASMfence)
    return unsafe_met;

  const abstract_eventt& first = egraph[back()];
  const abstract_eventt& second = egraph[*s_it];

  const data_dpt& data_dp = egraph.map_data_dp[first.thread];

  /* if data dp between linking the pair, safe */
  if(first.thread==second.thread && data_dp.dp(first,second))
    return unsafe_met;

  /* AC and BC conditions */
  if(first.thread!=second.thread && model==Power)
  {
    bool AC = false;
    bool BC = false;

    /* no fence after the second element? (AC) */
    const_iterator AC_it = ++s_it;
    --s_it;
    for(;
      AC_it!=end() && egraph[*AC_it].thread==second.thread;
      AC_it++)
      if(egraph[*AC_it].operation==abstract_eventt::ASMfence
        && egraph[*AC_it].is_cumul()
        && egraph[*AC_it].is_corresponding_fence(first, second))
      {
        AC = true;
        break;
      }

    if(AC)
      return unsafe_met;

    if(AC_it==end() && egraph[front()].thread==second.thread)
      for(AC_it=begin();
        !(egraph[*AC_it]==first) && egraph[*AC_it].thread==second.thread;
        AC_it++)
        if(egraph[*AC_it].operation==abstract_eventt::ASMfence
          && egraph[*AC_it].is_cumul()
          && egraph[*AC_it].is_corresponding_fence(first, second))
        {
          AC = true;
          break;
        }

    if(AC)
      return unsafe_met;

    /* no fence before the first element? (BC) */
    const_iterator BC_it = end();
    --BC_it;
    
    for(;
      BC_it!=begin() && egraph[*BC_it].thread==first.thread;
      BC_it--)
      if(egraph[*BC_it].operation==abstract_eventt::ASMfence
        && egraph[*BC_it].is_cumul()
        && egraph[*BC_it].is_corresponding_fence(first, second))
      {
        BC = true;
        break;
      }

    if(BC)
      return unsafe_met;

    if(BC_it==begin() && egraph[back()].thread==first.thread)
    {
      BC_it = end();
      BC_it--;
      for(;
        !(egraph[*BC_it]==second) && egraph[*BC_it].thread==first.thread;
        BC_it--)
        if(egraph[*BC_it].operation==abstract_eventt::ASMfence
          && egraph[*BC_it].is_cumul()
          && egraph[*BC_it].is_corresponding_fence(first, second))
        {
          BC = true;
          break;
        }
    }

    if(BC)
      return unsafe_met;
  }

  if(s_it==begin())
  {
    /* no lwfence between the pair */
    if(first.unsafe_pair(second,model) 
      && (first.thread!=second.thread || egraph.are_po_ordered(back(),*s_it)))
    {
      if(!fast)
      {
        const delayt delay(back(),*s_it,(first.thread==second.thread));
        unsafe_pairs.insert(delay);
      }
      return true;
    }
  }
  else
  {
    /* one (or more) lwfence between the pair */
    if(first.unsafe_pair_asm(second,model,fences_met)
      && (first.thread!=second.thread || egraph.are_po_ordered(back(),*s_it)))
    {
      if(!fast)
      {
        const delayt delay(back(),*s_it,(first.thread==second.thread));
        unsafe_pairs.insert(delay);
      }
      return true;
    }
  }

  return unsafe_met;
}

/*******************************************************************\

Function: event_grapht::critical_cyclet::is_not_uniproc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool event_grapht::critical_cyclet::is_not_uniproc() const
{
  const_iterator it = begin();

  /* find the first non-fence event */
  for(;
    it!=end() && (egraph[*it].operation==abstract_eventt::Fence
    || egraph[*it].operation==abstract_eventt::Lwfence
    || egraph[*it].operation==abstract_eventt::ASMfence); 
    it++);

  /* if only fences, uniproc */
  if(it==end())
    return false;

  const irep_idt& var = egraph[*it].variable;
  for(;
    it!=end() && (egraph[*it].variable==var 
    || egraph[*it].operation==abstract_eventt::Fence
    || egraph[*it].operation==abstract_eventt::Lwfence
    || egraph[*it].operation==abstract_eventt::ASMfence);
    it++);

  return (it!=end());
}

/*******************************************************************\

Function: event_grapht::critical_cyclet::is_not_thin_air

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool event_grapht::critical_cyclet::is_not_thin_air() const
{
  assert(size()>2);

  const_iterator it = begin();
  for(; it!=end() && ++it!=end(); it++)
  {
    --it;

    const abstract_eventt& current = egraph[*it];
    const abstract_eventt& next = egraph[*(++it)];

    --it;

    /* rf */
    if(current.operation==abstract_eventt::Write &&
      next.operation==abstract_eventt::Read)
      continue;

    /* data dependencies */
    const data_dpt& dep = egraph.map_data_dp[current.thread];

    if(dep.dp(current,next))
      continue;

    return true;
  }

  const abstract_eventt& current = egraph[back()];
  const abstract_eventt& next = egraph[front()];

  /* rf */
  if(current.operation==abstract_eventt::Write &&
    next.operation==abstract_eventt::Read)
     return false;

  /* data dependencies */
  const data_dpt& dep = egraph.map_data_dp[current.thread];

  if(dep.dp(current,next))
    return false;

  return true;
}

/*******************************************************************\

Function: event_grapht::critical_cyclet::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string event_grapht::critical_cyclet::print() const
{
  std::string cycle = "Cycle: ";
  for(const_iterator it=begin(); it!=end(); it++)
    cycle += i2string(egraph[*it].id) + "; ";
  return cycle + " End of cycle.";
}

/*******************************************************************\

Function: event_grapht::critical_cyclet::print_events

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string event_grapht::critical_cyclet::print_events() const
{
  std::string cycle = "Cycle: ";
  for(const_iterator it=begin(); it!=end(); it++)
    cycle += egraph[*it].get_operation() + id2string(egraph[*it].variable) 
      + "; ";
  return cycle + " End of cycle.";
}

/*******************************************************************\

Function: event_grapht::critical_cyclet::print_output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string event_grapht::critical_cyclet::print_output() const
{
  std::string cycle;
  for(const_iterator it=begin(); it!=end(); it++)
  {
    cycle += egraph[*it].variable.as_string() + " ("; 
    cycle += egraph[*it].location.as_string() + ") ";
  }
  return cycle;
}

/*******************************************************************\

Function: event_grapht::critical_cyclet::print_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string event_grapht::critical_cyclet::print_name(weak_memory_modelt model) const
{
  std::string name;
  const_iterator prev_it=end();
  for(const_iterator cur_it=begin(); cur_it!=end(); cur_it++)
  {
    const abstract_eventt& cur = egraph[*cur_it];

    if(prev_it!=end())
    {
      const abstract_eventt& prev = egraph[*prev_it];

      if(cur.operation == abstract_eventt::Fence)
      {
        abstract_eventt succ;
        if(++cur_it != end())
        {
          --cur_it;
          succ = egraph[ *(++cur_it) ];
          --cur_it;
        }
        else
        {
          --cur_it;
          succ = egraph[front()];
        }
        name += (model==Power?" Sync":" MFence"); 
        name += (prev.variable==cur.variable?"s":"d")
          + prev.get_operation() + succ.get_operation();
      }

      else if(cur.operation == abstract_eventt::Lwfence)
      {
        abstract_eventt succ;
        if(++cur_it != end())
        {
          --cur_it;
          succ = egraph[ *(++cur_it) ];
          --cur_it;
        }
        else
        {
          --cur_it;
          succ = egraph[front()];
        }
        name += " LwSync";
        name += (prev.variable==cur.variable?"s":"d")
          + prev.get_operation() + succ.get_operation();
      }

      else if(prev.variable == cur.variable
        && prev.operation == abstract_eventt::Write
        && cur.operation == abstract_eventt::Read)
      {
        name += " Rf";
        name += (prev.thread==cur.thread?"i":"e");
      }

      else if(prev.variable == cur.variable
        && prev.operation == abstract_eventt::Read
        && cur.operation == abstract_eventt::Write)
      {
        name += " Fr";
        name += (prev.thread==cur.thread?"i":"e");
      }

      else if(prev.variable == cur.variable
        && prev.operation == abstract_eventt::Write
        && cur.operation == abstract_eventt::Write
        && prev.thread != cur.thread) 
        /* we prefer to write Po rather than Wsi */
      {
        name += " Ws";
        name += (prev.thread==cur.thread?"i":"e");
      }

      else if(prev.thread == cur.thread
        && prev.operation != abstract_eventt::Fence)
      {
        name += " Po";
        name += (prev.variable==cur.variable?"s":"d") + prev.get_operation() 
          + cur.get_operation();
      }
    }

    prev_it = cur_it;
  }

  const abstract_eventt& first = egraph[front()];
  const abstract_eventt& last = egraph[back()];

  if(first.operation == abstract_eventt::Fence)
  {
    const_iterator next = begin();
    const abstract_eventt& succ= egraph[ *(++next) ];
    name += (model==Power?" Sync":" MFence");
    name += (last.variable==first.variable?"s":"d")
      + last.get_operation() + succ.get_operation();
  }

  else if(first.operation == abstract_eventt::Lwfence)
  {
    const_iterator next = begin();
    const abstract_eventt& succ= egraph[ *(++next) ];
    name += " LwSync";
    name += (last.variable==first.variable?"s":"d") 
      + last.get_operation() + succ.get_operation();
  }

  else if(last.variable == first.variable
    && last.operation == abstract_eventt::Write
    && first.operation == abstract_eventt::Read)
  {
    name += " Rf";
    name += (last.thread==first.thread?"i":"e");
  }

  else if(last.variable == first.variable
    && last.operation == abstract_eventt::Read
    && first.operation == abstract_eventt::Write)
  {
    name += " Fr";
    name += (last.thread==first.thread?"i":"e");
  }

  else if(last.variable == first.variable
    && last.operation == abstract_eventt::Write
    && first.operation == abstract_eventt::Write
    && last.thread != first.thread) 
    /* we prefer to write Po rather than Wsi */
  {
    name += " Ws";
    name += (last.thread==first.thread?"i":"e");
  }

  else if(last.thread==first.thread
    && last.operation != abstract_eventt::Fence)
  {
    name += " Po";
    name += (last.variable==first.variable?"s":"d") + last.get_operation() 
      + first.get_operation();
  }

  return name;
}

/*******************************************************************\

Function: event_grapht::critical_cyclet::print_dot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void event_grapht::critical_cyclet::print_dot(
  std::ofstream& str, unsigned colour, weak_memory_modelt model) const
{
  /* print vertices */
  for(const_iterator it=begin(); it!=end(); it++)
  {
    const abstract_eventt& ev = egraph[*it];

    /* id of the cycle in comments */
    str << "/* " << id << " */" << std::endl;

    /* vertex */
    str << ev.id << "[label=\"\\\\lb {" << ev.id << "}" << ev.get_operation();
    str << "{" << ev.variable << "} {} @thread" << ev.thread << "\"];";
    str << std::endl;
  }

  /* print edges */
  const_iterator prev_it=end();
  for(const_iterator cur_it=begin(); cur_it!=end(); cur_it++)
  {
    const abstract_eventt& cur = egraph[*cur_it];

    /* id of the cycle in comments */
    str << "/* " << id << " */" << std::endl;

    /* edge */
    if(prev_it!=end())
    {
      const abstract_eventt& prev = egraph[*prev_it];

      str << prev.id << "->";
      if(cur.operation == abstract_eventt::Fence)
      {
        abstract_eventt succ;
        if(++cur_it != end())
        {
          --cur_it;
          succ = egraph[ *(++cur_it) ];
          --cur_it;
        }
        else
        {
          --cur_it;
          succ = egraph[front()];
        }
        str << succ.id << "[label=\"";
        str << (model==Power?"Sync":"MFence"); 
        str << (prev.variable==cur.variable?"s":"d");
        str << prev.get_operation() << succ.get_operation();
      }

      else if(cur.operation == abstract_eventt::Lwfence)
      {
        abstract_eventt succ;
        if(++cur_it != end())
        {
          --cur_it;
          succ = egraph[ *(++cur_it) ];
          --cur_it;
        }
        else
        {
          --cur_it;
          succ = egraph[front()];
        }
        str << succ.id << "[label=\"";
        str << "LwSync" << (prev.variable==cur.variable?"s":"d");
        str  <<prev.get_operation() << succ.get_operation();
      }

      else if(prev.variable == cur.variable
        && prev.operation == abstract_eventt::Write
        && cur.operation == abstract_eventt::Read)
      {
        str << cur.id << "[label=\"";
        str << "Rf" << (prev.thread==cur.thread?"i":"e");
      }
      else if(prev.variable == cur.variable
        && prev.operation == abstract_eventt::Read
        && cur.operation == abstract_eventt::Write)
      {
        str << cur.id << "[label=\"";
        str << "Fr" << (prev.thread==cur.thread?"i":"e");
      }

      else if(prev.variable == cur.variable
        && prev.operation == abstract_eventt::Write
        && cur.operation == abstract_eventt::Write
        && prev.thread != cur.thread)
        /* we prefer to write Po rather than Wsi */
      {
        str << cur.id << "[label=\"";
        str << "Ws" << (prev.thread==cur.thread?"i":"e");
      }

      else if(prev.thread == cur.thread
        && prev.operation != abstract_eventt::Fence)
      {
        str << cur.id << "[label=\"";
        str << "Po" << (prev.variable==cur.variable?"s":"d") 
          + prev.get_operation() + cur.get_operation();
      }

      else
        str << cur.id << "[label=\"?";

      str << "\",color=" << print_colour(colour) << "];" <<std::endl;
    }

    prev_it = cur_it;
  }

  const abstract_eventt& first = egraph[front()];
  const abstract_eventt& last = egraph[back()];

  /* id of the cycle in comments */
  str << "/* " << id << " */" << std::endl;

  /* edge */
  str << last.id << "->";
  if(first.operation == abstract_eventt::Fence)
  {
    const_iterator next = begin();
    const abstract_eventt& succ= egraph[ *(++next) ];
    str << succ.id << "[label=\"";
    str << (model==Power?"Sync":"MFence");
    str << (last.variable==first.variable?"s":"d");
    str << last.get_operation() << succ.get_operation();
  }

  else if(first.operation == abstract_eventt::Lwfence)
  {
    const_iterator next = begin();
    const abstract_eventt& succ= egraph[ *(++next) ];
    str << succ.id << "[label=\"";
    str << "LwSync" << (last.variable==first.variable?"s":"d");
    str << last.get_operation() << succ.get_operation();
  }

  else if(last.variable == first.variable
    && last.operation == abstract_eventt::Write
    && first.operation == abstract_eventt::Read)
  {
    str << first.id << "[label=\"";
    str << "Rf" << (last.thread==first.thread?"i":"e");
  }

  else if(last.variable == first.variable
    && last.operation == abstract_eventt::Read
    && first.operation == abstract_eventt::Write)
  {
    str << first.id << "[label=\"";
    str << "Fr" << (last.thread==first.thread?"i":"e");
  }

  else if(last.variable == first.variable
    && last.operation == abstract_eventt::Write
    && first.operation == abstract_eventt::Write
    && last.thread != first.thread)
    /* we prefer to write Po rather than Wsi */
  {
    str << first.id << "[label=\"";
    str << "Ws" << (last.thread==first.thread?"i":"e");
  }

  else if(last.thread==first.thread
    && last.operation != abstract_eventt::Fence)
  {
    str << first.id << "[label=\"";
    str << "Po" << (last.variable==first.variable?"s":"d");
    str << last.get_operation() << first.get_operation();
  }

  else
    str << first.id << "[label=\"?";

  str << "\", color=" << print_colour(colour) << "];" <<std::endl;
}

/*******************************************************************\

Function: data_dpt::dp_analysis

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void data_dpt::dp_analysis(
  const datat& read, 
  bool local_read, 
  const datat& write, 
  bool local_write)
{
  std::set<data_classt>::iterator class_it;
  datat read_p;
  datat write_p;

  if(local_read)
    read_p = datat(read.first, locationt());
  else
    read_p = read;

  if(local_write)
    write_p = datat(write.first, locationt());
  else
    write_p = write;

  for(class_it=dependencies.begin();
    class_it!=dependencies.end();
    class_it++)
  {
    if(local_read
      && class_it->find(read_p)!=class_it->end())
    {
      data_classt new_class(*class_it);
      new_class.insert(write_p);
      dependencies.erase(class_it);
      dependencies.insert(new_class);
      continue;
    }

    if(local_write
      && class_it->find(write_p)!=class_it->end())
    {
      data_classt new_class(*class_it);
      new_class.insert(read_p);
      dependencies.erase(class_it);
      dependencies.insert(new_class);
      continue;
    }
  }

  if(class_it==dependencies.end())
  {
    data_classt new_class;
    new_class.insert(read_p);
    new_class.insert(write_p);
    dependencies.insert(new_class);
  }
}

/*******************************************************************\

Function: data_dpt::dp_analysis

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void data_dpt::dp_analysis(const abstract_eventt& read, 
  const abstract_eventt& write)
{
  datat d_read(read.variable,read.location);
  datat d_write(write.variable,write.location);
  dp_analysis(d_read,read.local,d_write,write.local);
}

/*******************************************************************\

Function: data_dpt::dp

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool data_dpt::dp(const abstract_eventt& e1, const abstract_eventt& e2) const
{
  datat d_e1(e1.variable, e1.location);
  datat d_e2(e2.variable, e2.location);

  if(e1.local)
    d_e1.second = locationt();

  if(e2.local)
    d_e2.second = locationt();

  for(std::set<data_classt>::iterator class_it=dependencies.begin();
    class_it!=dependencies.end(); class_it++)
    if(class_it->find(d_e1) != class_it->end()
      && class_it->find(d_e2) != class_it->end()
      && e1.thread == e2.thread && e1.variable != e2.variable)
      return true;

  return false;
}

/*******************************************************************\

Function: data_dpt::dp_merge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void data_dpt::dp_merge()
{
  /* let's take two distinct classes C1 and C2 */
  for(std::set<data_classt>::iterator class_it=dependencies.begin();
      class_it!=dependencies.end();
      class_it++)
  {
    std::set<data_classt>::iterator class_plus_one = class_it;
    class_plus_one++;

    for(std::set<data_classt>::iterator class_it2=class_plus_one;
        class_it2!=dependencies.end();
        class_it2++)
    {
      bool next = false;

      /* if C1 has an element in C2, merge C1 and C2 */
      for(data_classt::iterator el_it=class_it->begin();
          el_it!=class_it->end();
          el_it++)
        if(el_it->second == locationt() 
          && class_it2->find(*el_it)!=class_it2->end())
        {
          /* create a new class C3=C1 U C2, then delete C1 and C2 */
          data_classt new_class(*class_it);
          new_class(*class_it2);
          dependencies.insert(new_class);
          /* TO FIX? */
          //dependencies.erase(class_it);
          //dependencies.erase(class_it2);
          next = true;
          //break;
        }

      if(next)
        break;

      /* if C2 has an element in C1, merge C1 and C2 */
      for(data_classt::iterator el_it2=class_it2->begin();
          el_it2!=class_it2->end();
          el_it2++)
        if(el_it2->second == locationt() 
          && class_it->find(*el_it2)!=class_it->end())
        {
          /* create a new class C3=C1 U C2, then delete C1 and C2 */
          data_classt new_class(*class_it);
          new_class(*class_it2);
          dependencies.insert(new_class);
          /* TO FIX? */
          //dependencies.erase(class_it);
          //dependencies.erase(class_it2);
          next = true;
          //break;
        }

       if(next)
         break;
    }
  }
}

/*******************************************************************\

Function: data_dpt::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void data_dpt::print()
{
  for(std::set<data_classt>::iterator class_it=dependencies.begin();
    class_it!=dependencies.end();
    class_it++)
  {
    DEBUG_MESSAGE("CLASS OF EQUIVALENCE");
    for(data_classt::iterator it=class_it->begin();
      it!=class_it->end();
      it++)
      DEBUG_MESSAGE(" "<<it->first<<" #"<<it->second);
  }
}

/*******************************************************************\

Function: event_grapht::graph_explorert::collect_cycles

  Inputs:

 Outputs:

 Purpose: Tarjan 1972 adapted and modified for events

\*******************************************************************/

void event_grapht::graph_explorert::collect_cycles(
  std::set<critical_cyclet>& set_of_cycles, 
  weak_memory_modelt model)
{
  /* all the events initially unmarked */
  for(unsigned i = 0; i<egraph.size(); i++)
    mark[i] = false;

  std::list<unsigned>* order;
  /* on Power, rfe pairs are also unsafe */
  if(model == TSO || model == PSO || model == RMO)
    order = &egraph.po_order;
  else
    order = &egraph.poUrfe_order;

  if(order->empty())
    return;

  /* if we only consider a limited part of the graph */
  order = order_filtering(order);

  if(order->empty())
    return;

  for(std::list<unsigned>::const_iterator st_it=order->begin(); 
    st_it!=order->end(); st_it++)
  {
    unsigned source = *st_it;
    DEBUG_MESSAGE("explore " << egraph[source].id);
    backtrack(set_of_cycles, source, source, 
      false, max_po_trans, false, false, model);

    while(!marked_stack.empty())
    {
      unsigned up = marked_stack.top();
      mark[up] = false;
      marked_stack.pop();
    }
  }
}

/*******************************************************************\

Function: event_grapht::graph_explorert::extract_cycle

  Inputs:

 Outputs:

 Purpose: see event_grapht::collect_cycles

\*******************************************************************/

event_grapht::critical_cyclet event_grapht::graph_explorert::extract_cycle(
  unsigned vertex, 
  unsigned source,
  unsigned number)
{
  critical_cyclet new_cycle(egraph,number);
  bool incycle = false;
  std::stack<unsigned> stack(point_stack);

  while(!stack.empty())
  {
    unsigned current_vertex = stack.top();
    stack.pop();

    DEBUG_MESSAGE("extract: " << egraph[current_vertex].get_operation() 
      << egraph[current_vertex].variable << "@" 
      << egraph[current_vertex].thread << "~" << egraph[current_vertex].local);

    if(current_vertex==vertex)
      incycle = true;

    if(incycle)
      new_cycle.push_front(current_vertex);

    if(current_vertex==source)
      break;
  }

  return new_cycle;
}

/*******************************************************************\

Function: event_grapht::graph_explorert::backtrack

  Inputs: get_po_only: used for po-transitivity

 Outputs:

 Purpose: see event_grapht::collect_cycles

\*******************************************************************/

bool event_grapht::graph_explorert::backtrack(
  std::set<critical_cyclet> &set_of_cycles, 
  unsigned source, 
  unsigned vertex,
  bool unsafe_met, /* unsafe pair for the model met in the visited path */
  unsigned po_trans, /* po-transition skips still allowed */
  bool same_var_pair, /* in a thread, tells if we already met one rfi wsi fri */
  bool lwfence_met, /* if we try to skip a lwsync (only valid for lwsyncWR) */
  weak_memory_modelt model)
{
  if(filtering(vertex))
    return false;

  DEBUG_MESSAGE("bcktck "<<egraph[vertex].id<<"#"<<vertex<<", "
    <<egraph[source].id<<"#"<<source);
  bool f = false;
  bool get_com_only = false;
  bool unsafe_met_updated = unsafe_met;
  bool same_var_pair_updated = same_var_pair;

  bool not_thin_air = true;

  const abstract_eventt& this_vertex = egraph[vertex];

  /* if specified, maximum number of events reached */
  if(max_var!=0 && point_stack.size()>max_var*3)
    return false;

  /* we only explore shared variables */
  if(!this_vertex.local)
  {
    /* only the lwsyncWR can be interpreted as poWR (i.e., skip of the fence */
    if(lwfence_met && this_vertex.operation!=abstract_eventt::Read)
      return false;

    /* no more than 4 events per thread */
    if(this_vertex.operation!=abstract_eventt::Fence
      && this_vertex.operation!=abstract_eventt::Lwfence)
    {
      if(events_per_thread[this_vertex.thread]==4)
        return false;
      else
        events_per_thread[this_vertex.thread]++;
    }

    /* constraint 1.a: there is at most one pair of events per thread
       with different variables. Given that we cannot have more than
       three events on the same variable, with two in the same thread,
       this means that we can have at most 2 consecutive events by po
       with the same variable, and two variables per thread (fences are
       not taken into account) */
    if(!point_stack.empty() && egraph.are_po_ordered(point_stack.top(),vertex)
      && this_vertex.operation!=abstract_eventt::Fence
      && this_vertex.operation!=abstract_eventt::Lwfence
      && this_vertex.variable==egraph[point_stack.top()].variable)
    {
      if(same_var_pair || 
        (this_vertex.operation==abstract_eventt::Read 
        && egraph[point_stack.top()].operation==abstract_eventt::Read))
      {
        events_per_thread[this_vertex.thread]--;
        return false;
      }
      else
      {
        same_var_pair_updated = true;
        if(events_per_thread[this_vertex.thread]>=3)
          get_com_only = true;
      }
    }

    /* constraint 1.b */
    if(!point_stack.empty() && egraph.are_po_ordered(point_stack.top(),vertex)
      && this_vertex.operation!=abstract_eventt::Fence
      && this_vertex.operation!=abstract_eventt::Lwfence
      && this_vertex.variable!=egraph[point_stack.top()].variable)
    {
      same_var_pair_updated = false;
    }

    /* constraint 2: per variable, either W W, R W, W R, or R W R */
    if(this_vertex.operation!=abstract_eventt::Fence 
      && this_vertex.operation!=abstract_eventt::Lwfence)
    {
      const unsigned char nb_writes = writes_per_variable[this_vertex.variable];
      const unsigned char nb_reads = reads_per_variable[this_vertex.variable];

      if(nb_writes+nb_reads==3)
      {
        events_per_thread[this_vertex.thread]--;
        return false;
      }
      else if(this_vertex.operation==abstract_eventt::Write)
      {
        if(nb_writes==2)
        {
          events_per_thread[this_vertex.thread]--;
          return false;
        }
        else
          writes_per_variable[this_vertex.variable]++;
      }
      else if(this_vertex.operation==abstract_eventt::Read)
      {
        if(nb_reads==2)
        {
          events_per_thread[this_vertex.thread]--;
          return false;
        }
        else
          reads_per_variable[this_vertex.variable]++;
      }
    }

    if(!point_stack.empty())
    {
      const abstract_eventt& prev_vertex = egraph[point_stack.top()];
      unsafe_met_updated |= (prev_vertex.unsafe_pair(this_vertex,model)
        && !(prev_vertex.thread==this_vertex.thread
          && egraph.map_data_dp[this_vertex.thread].dp(prev_vertex,this_vertex)));
    }

    point_stack.push(vertex);
    mark[vertex]=true;
    marked_stack.push(vertex);

    if(!get_com_only)
    {
      /* we first visit via po transition, if existing */
      for(graph<abstract_eventt>::edgest::const_iterator 
        w_it=egraph.po_out(vertex).begin(); 
        w_it!=egraph.po_out(vertex).end(); w_it++)
      {
        const unsigned w = w_it->first;
        if(w < source)
          egraph.remove_po_edge(vertex,w);
        else if(w == source && point_stack.size()>=4
          && (unsafe_met_updated
            || this_vertex.unsafe_pair(egraph[source],model)) )
        {
          critical_cyclet new_cycle = extract_cycle(vertex, source, cycle_nb++);
          not_thin_air = new_cycle.is_not_thin_air();
          if(new_cycle.is_not_uniproc() && not_thin_air
            && (new_cycle.is_unsafe(model)||new_cycle.is_unsafe_asm(model)))
          {
            DEBUG_MESSAGE(new_cycle.print_name(model));
            set_of_cycles.insert(new_cycle);
          }
          f = true;
        }
        else if(!mark[w])
          f |= backtrack(set_of_cycles, source, w, unsafe_met_updated, 
            po_trans, same_var_pair_updated, false, model);
      }
    }

    /* we then visit via com transitions, if existing */
    for(graph<abstract_eventt>::edgest::const_iterator 
      w_it=egraph.com_out(vertex).begin();
      w_it!=egraph.com_out(vertex).end(); w_it++)
    {
      const unsigned w = w_it->first;
      if(w < source)
        egraph.remove_com_edge(vertex,w);
      else if(w == source && point_stack.size()>=4
        && (unsafe_met_updated 
          || this_vertex.unsafe_pair(egraph[source],model)) )
      {
        critical_cyclet new_cycle = extract_cycle(vertex, source, cycle_nb++);
        not_thin_air = new_cycle.is_not_thin_air();
        if(new_cycle.is_not_uniproc() && not_thin_air 
          && (new_cycle.is_unsafe(model)||new_cycle.is_unsafe_asm(model)))
        {
          DEBUG_MESSAGE(new_cycle.print_name(model));
          set_of_cycles.insert(new_cycle);
        }
        f = true;
      }
      else if(!mark[w])
        f |= backtrack(set_of_cycles, source, w, 
          unsafe_met_updated, po_trans, false, false, model);
    }

    if(f)
    {
      assert(!marked_stack.empty());
      while(marked_stack.top()!=vertex)
      {
        unsigned up = marked_stack.top();
        marked_stack.pop();
        mark[up] = false;
      }

      marked_stack.pop();
      mark[vertex] = false;
    }

    assert(!point_stack.empty());
    point_stack.pop();

    /* removes variable access */
    if(this_vertex.operation!=abstract_eventt::Fence 
      && this_vertex.operation!=abstract_eventt::Lwfence)
    {
      if(this_vertex.operation==abstract_eventt::Write)
        writes_per_variable[this_vertex.variable]--;
      else
        reads_per_variable[this_vertex.variable]--;

      events_per_thread[this_vertex.thread]--;
    }
  }

  /* transitivity of po: do the same, but skip this event 
     (except if it is a fence or no more po-transition skips allowed);
     if the cycle explored so far has a thin-air subcycle, this cycle
     is not valid: stop this exploration here */
  if( not_thin_air
    && !get_com_only && (po_trans > 1 || po_trans==0)
    && !point_stack.empty() && egraph.are_po_ordered(point_stack.top(),vertex)
    && this_vertex.operation!=abstract_eventt::Fence
    && ( this_vertex.operation!=abstract_eventt::Lwfence
      || egraph[point_stack.top()].operation==abstract_eventt::Write)
    )
  {
    mark[vertex]=true;
    marked_stack.push(vertex);

    const bool is_lwfence = (this_vertex.operation==abstract_eventt::Lwfence
      && egraph[point_stack.top()].operation==abstract_eventt::Write);

    for(graph<abstract_eventt>::edgest::const_iterator w_it=
      egraph.po_out(vertex).begin();
      w_it!=egraph.po_out(vertex).end(); w_it++)
    {
      const unsigned w = w_it->first;
      f |= backtrack(set_of_cycles, source, w,
        unsafe_met_updated, (po_trans==0?0:po_trans-1), 
        same_var_pair_updated, is_lwfence, model);
    }

    if(f)
    {
      assert(!marked_stack.empty());
      while(marked_stack.top()!=vertex)
      {
        unsigned up = marked_stack.top();
        marked_stack.pop();
        mark[up] = false;
      }

      marked_stack.pop();
      mark[vertex] = false;
    }
  }

  return f;
}

/*******************************************************************\

Function: test

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

/* ipw23 hidden in a graph */
void test2()
{
  abstract_eventt a(abstract_eventt::Write, 1, "x", 1, locationt(),false);
  abstract_eventt b(abstract_eventt::Read, 1, "y", 2, locationt(),false);
  abstract_eventt c(abstract_eventt::Write, 2, "y", 3, locationt(),false);
  abstract_eventt d(abstract_eventt::Read, 2, "x", 4, locationt(),false);
  abstract_eventt r(abstract_eventt::Write, 1, "y", 5, locationt(),false);

  event_grapht graph;

  unsigned a_node = graph.add_node();
  graph[a_node](a);
  unsigned b_node = graph.add_node();
  graph[b_node](b);
  unsigned c_node = graph.add_node();
  graph[c_node](c);
  unsigned d_node = graph.add_node();
  graph[d_node](d);
  unsigned r_node = graph.add_node();
  graph[r_node](r);

  graph.add_po_edge(a_node,b_node);
  graph.add_po_edge(c_node,d_node);
  graph.add_po_edge(r_node,a_node);
  graph.add_com_edge(b_node,c_node);
  graph.add_com_edge(d_node,a_node);

  std::set<event_grapht::critical_cyclet> set;
  graph.collect_cycles(set, Power);
  for(std::set<event_grapht::critical_cyclet>::iterator it=set.begin(); 
    it!=set.end(); it++)
    if(it->is_not_uniproc() && it->is_not_thin_air())
      std::cout << it->print_name(Power) << std::endl;

  std::cout << "test 2 successful" << std::endl;
}

/* ipw23 */
void test1() 
{
  abstract_eventt a(abstract_eventt::Write, 1, "x", 1, locationt(),false);
  abstract_eventt b(abstract_eventt::Read, 1, "y", 2, locationt(),false);
  abstract_eventt c(abstract_eventt::Write, 2, "y", 3, locationt(),false);
  abstract_eventt d(abstract_eventt::Read, 2, "x", 4, locationt(),false);

  event_grapht graph;

  unsigned a_node = graph.add_node();
  graph[a_node](a);
  unsigned b_node = graph.add_node();
  graph[b_node](b);
  unsigned c_node = graph.add_node();
  graph[c_node](c);
  unsigned d_node = graph.add_node();
  graph[d_node](d);

  graph.add_po_edge(a_node,b_node);
  graph.add_po_edge(c_node,d_node);
  graph.add_com_edge(b_node,c_node);
  graph.add_com_edge(d_node,a_node);

  std::set<event_grapht::critical_cyclet> set;
  graph.collect_cycles(set, Power);
  for(std::set<event_grapht::critical_cyclet>::iterator it=set.begin(); 
    it!=set.end(); it++)
    if(it->is_not_uniproc() && it->is_not_thin_air())
      std::cout << it->print_name(Power) << std::endl;

  std::cout << "test 1 successful" << std::endl;
  test2();
}

/* iriw */
void test()
{
  abstract_eventt a(abstract_eventt::Read, 1, "x", 1, locationt(),false);
  abstract_eventt b(abstract_eventt::Read, 1, "y", 2, locationt(),false);
  abstract_eventt c(abstract_eventt::Read, 2, "y", 3, locationt(),false);
  abstract_eventt d(abstract_eventt::Read, 2, "x", 4, locationt(),false);
  abstract_eventt e(abstract_eventt::Write, 3, "x", 5, locationt(),false);
  abstract_eventt f(abstract_eventt::Write, 4, "y", 6, locationt(),false);

  event_grapht graph;

  unsigned a_node = graph.add_node();
  graph[a_node](a);
  unsigned b_node = graph.add_node();
  graph[b_node](b);
  unsigned c_node = graph.add_node();
  graph[c_node](c);
  unsigned d_node = graph.add_node();
  graph[d_node](d);
  unsigned e_node = graph.add_node();
  graph[e_node](e);
  unsigned f_node = graph.add_node();
  graph[f_node](f);

  graph.add_po_edge(a_node,b_node);
  graph.add_po_edge(c_node,d_node);
  graph.add_com_edge(b_node,f_node);
  graph.add_com_edge(f_node,c_node);
  graph.add_com_edge(d_node,e_node);
  graph.add_com_edge(e_node,a_node);

  std::set<event_grapht::critical_cyclet> set;
  graph.collect_cycles(set, Power);
  for(std::set<event_grapht::critical_cyclet>::iterator it=set.begin(); 
    it!=set.end(); it++)
    if(it->is_not_uniproc() && it->is_not_thin_air())
      std::cout << it->print_name(Power) << std::endl;

  std::cout << "test 0 successful" << std::endl;
  test1();
}
