/*******************************************************************\

Module: graph of abstract events

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

#include "event_graph.h"

#include <util/i2string.h>
#include <fstream>

//#define DEBUG
//#define ASMFENCE

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

Function: event_grapht::copy_segment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned event_grapht::copy_segment(unsigned begin, unsigned end)
{
  // TODO
  return end;  
}

/*******************************************************************\

Function: event_grapht::critical_cyclet::check_AC

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool event_grapht::critical_cyclet::check_AC(
  const_iterator s_it, 
  const abstract_eventt& first, 
  const abstract_eventt& second) const
{
  bool AC=false;
  const_iterator AC_it=s_it;
  ++AC_it;
  for(; AC_it!=end(); ++AC_it)
  {
    const abstract_eventt& AC_evt=egraph[*AC_it];
    if(AC_evt.operation==abstract_eventt::Fence)
    {
      AC=true;
      break;
    }
    if(AC_evt.thread!=second.thread)
      break;
  }

  if(AC)
    return true;

  if(AC_it==end() && egraph[front()].thread==second.thread)
    for(AC_it=begin(); ; ++AC_it)
    {
      const abstract_eventt& AC_evt=egraph[*AC_it];
      if(AC_evt.operation==abstract_eventt::Fence)
      {
        AC=true;
        break;
      }
      if(AC_evt==first || AC_evt.thread!=second.thread)
        break;
    }

  return AC;
}

/*******************************************************************\

Function: event_grapht::critical_cyclet::check_BC

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool event_grapht::critical_cyclet::check_BC(
  const_iterator it,
  const abstract_eventt& first, 
  const abstract_eventt& second) const
{
  bool BC=false;
  /* no fence before the first element? (BC) */
  const_iterator BC_it;
  if(it==begin())
  {
    BC_it=end();
    --BC_it;
  }
  else
  {
    BC_it=it;
    --BC_it;
  }
  for(; BC_it!=begin(); --BC_it)
  {
    const abstract_eventt& BC_evt=egraph[*BC_it];
    if(BC_evt.operation==abstract_eventt::Fence)
    {
      BC=true;
      break;
    }
    if(BC_evt.thread!=first.thread)
      break;
  }

  if(BC)
    return true;

  if(BC_it==begin() && egraph[back()].thread==first.thread)
  {
    BC_it=end();
    --BC_it;
    for(; ; --BC_it)
    {
      const abstract_eventt& BC_evt=egraph[*BC_it];
      if(BC_evt.operation==abstract_eventt::Fence)
      {
        BC=true;
        break;
      }
      if(BC_evt==second || BC_evt.thread!=first.thread)
        break;
    }
  }

  return BC;
}

/*******************************************************************\

Function: event_grapht::critical_cyclet::is_unsafe

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool event_grapht::critical_cyclet::is_unsafe(memory_modelt model, bool fast)
{
  DEBUG_MESSAGE("cycle is safe?");
  bool unsafe_met=false;

  /* critical cycles contain at least 4 events */
  assert(size()>=4);

  /* critical cycles contain at least 2 threads */
  unsigned thread=egraph[*begin()].thread;
  const_iterator th_it;
  for(th_it=begin(); 
    th_it!=end() && thread==egraph[*th_it].thread; ++th_it)
    thread = egraph[*th_it].thread;
  if(th_it==end())
    return false;

  /* selects the first element of the pair */
  const_iterator it=begin();
  const_iterator next=it;
  ++next;
  for(; it!=end() && next!=end(); ++next, ++it)
  {
    const abstract_eventt& it_evt=egraph[*it];
    const abstract_eventt& next_evt=egraph[*next];

    /* strong fence -- this pair is safe */
    if(it_evt.operation==abstract_eventt::Fence)
      continue;

    if(next_evt.operation==abstract_eventt::Fence)
      continue;

    /* first element is a weak fence */
    if(it_evt.operation==abstract_eventt::Lwfence)
      continue;

    /* selects the next event which is not a weak fence */
    const_iterator s_it=next;

    for(; s_it!=end() && egraph[*s_it].operation==abstract_eventt::Lwfence; 
      ++s_it);

    if(s_it==end())
      continue;

    const abstract_eventt& s_evt=egraph[*s_it];

    if(s_evt.operation==abstract_eventt::Fence)
      continue;

    /* if the whole cycle has been explored */
    if(it==s_it)
      continue;

    const abstract_eventt& first=it_evt;
    const abstract_eventt& second=s_evt;
    const data_dpt& data_dp=egraph.map_data_dp[first.thread];

    /* if data dp between linking the pair, safe */
    if(first.thread==second.thread && data_dp.dp(first,second))
      continue;

    /* AC and BC conditions */
    if(first.thread!=second.thread && model==Power)
    {
      if(check_AC(s_it, first, second))
        continue;

      if(check_BC(it, first, second))
        continue;
    }

    const_iterator n_it=it;
    ++n_it;
    if(s_it==n_it)
    {
      /* there is no lwfence between the pair */
      if(first.unsafe_pair(second,model) 
        && (first.thread!=second.thread || egraph.are_po_ordered(*it,*s_it)))
      {
        const_iterator before_first;
        const_iterator after_second;

        if(it==begin())
          before_first=end();
        else
          before_first=it;
        --before_first;

        n_it=s_it;
        ++n_it;
        if(n_it==end())
          after_second=begin();
        else
          after_second=s_it;

        if(first.variable == second.variable 
          && first.thread == second.thread
          && egraph[*before_first].thread != first.thread
          && egraph[*after_second].thread != second.thread)
        {
          /* not unsafe */
        }
        else
        {
          if(fast)
            return true;
          else
          {
            const delayt delay(*it,*s_it,(first.thread==second.thread));
            unsafe_pairs.insert(delay);
            unsafe_met=true;
          }
        }
      }
    }
    else
    {
      /* one (or more) lwfence between the pair */
      if(first.unsafe_pair_lwfence(second,model)
        && (first.thread!=second.thread || egraph.are_po_ordered(*it,*s_it)))
      {
        const_iterator before_first;
        const_iterator after_second;

        if(it==begin())
          before_first=end();
        else
          before_first=it;
        --before_first;

        n_it=s_it;
        ++n_it;
        if(n_it==end())
          after_second=begin();
        else
          after_second=s_it;

        if(first.variable == second.variable
          && first.thread == second.thread
          && egraph[*before_first].thread != first.thread
          && egraph[*after_second].thread != second.thread)
        {
          /* not unsafe */
        }
        else
        {
          if(fast)
            return true;
          else
          {
            const delayt delay(*it,*s_it,(first.thread==second.thread));
            unsafe_pairs.insert(delay);
            unsafe_met=true;
          }
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
    if(check_AC(s_it, first, second))
      return unsafe_met;

    if(check_BC(begin(), first, second))
      return unsafe_met;
  }

  if(s_it==begin())
  {
    /* no lwfence between the pair */
    if(first.unsafe_pair(second,model) 
      && (first.thread!=second.thread || egraph.are_po_ordered(back(),*s_it)))
    {
      std::list<unsigned>::const_iterator before_first;
      std::list<unsigned>::const_iterator after_second;

      before_first = end();
      --before_first;
      --before_first;

      after_second = s_it;
      ++after_second;

      if(first.variable == second.variable
        && first.thread == second.thread
        && egraph[*before_first].thread != first.thread
        && egraph[*after_second].thread != second.thread)
      {
        /* not unsafe */
      }
      else
      {
        if(!fast)
        {
          const delayt delay(back(),*s_it,(first.thread==second.thread));
          unsafe_pairs.insert(delay);
        }
        return true;
      }
    }
  }
  else
  {
    /* one (or more) lwfence between the pair */
    if(first.unsafe_pair_lwfence(second,model)
      && (first.thread!=second.thread || egraph.are_po_ordered(back(),*s_it)))
    {
      std::list<unsigned>::const_iterator before_first;
      std::list<unsigned>::const_iterator after_second;
      
      before_first = end();
      --before_first;
      --before_first;

      after_second = s_it;
      ++after_second;
    
      if(first.variable == second.variable
        && first.thread == second.thread
        && egraph[*before_first].thread != first.thread
        && egraph[*after_second].thread != second.thread)
      {
        /* not unsafe */
      }
      else
      {
        if(!fast)
        {
          const delayt delay(back(),*s_it,(first.thread==second.thread));
          unsafe_pairs.insert(delay);
        }
      return true;
      }
    }
  }

  return unsafe_met;
}

/*******************************************************************\

Function: event_grapht::critical_cyclet::is_unsafe_asm

  Inputs:

 Outputs:

 Purpose: same as is_unsafe, but with ASM fences

\*******************************************************************/

bool event_grapht::critical_cyclet::is_unsafe_asm(memory_modelt model, 
  bool fast)
{
  DEBUG_MESSAGE("cycle is safe?");
  bool unsafe_met = false;
  unsigned char fences_met = 0;

  /* critical cycles contain at least 4 events */
  if(size()<4)
    return false;

  /* critical cycles contain at least 2 threads */
  unsigned thread = egraph[*begin()].thread;
  const_iterator th_it;
  for(th_it=begin(); 
    th_it!=end() && thread==egraph[*th_it].thread; ++th_it)
    thread = egraph[*th_it].thread;
  if(th_it==end())
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
  const_iterator it=begin();

  /* find the first non-fence event */
  for(; it!=end(); ++it)
  {
    const abstract_eventt& it_evt=egraph[*it];
    if(it_evt.operation!=abstract_eventt::Fence
      && it_evt.operation!=abstract_eventt::Lwfence
      && it_evt.operation!=abstract_eventt::ASMfence)
      break;
  }

  /* if only fences, uniproc */
  if(it==end())
    return false;

  const irep_idt& var=egraph[*it].variable;
  for(; it!=end(); ++it)
  {
    const abstract_eventt& it_evt=egraph[*it];
    if(it_evt.variable!=var
      && it_evt.operation!=abstract_eventt::Fence
      && it_evt.operation!=abstract_eventt::Lwfence
      && it_evt.operation!=abstract_eventt::ASMfence)
      break;
  }

  return (it!=end());
}

/*******************************************************************\

Function: event_grapht::critical_cyclet::is_not_weak_uniproc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool event_grapht::critical_cyclet::is_not_weak_uniproc() const
{
  const_iterator it=begin();

  /* find the first non-fence event */
  for(; it!=end(); it++)
  {
    const abstract_eventt& it_evt=egraph[*it];
    if(it_evt.operation!=abstract_eventt::Fence
      && it_evt.operation!=abstract_eventt::Lwfence
      && it_evt.operation!=abstract_eventt::ASMfence)
      break;
  }

  /* if only fences, uniproc */
  if(it==end())
    return false;

  const irep_idt& var=egraph[*it].variable;

  const_iterator prev=it;
  for(; it!=end(); prev=it, ++it)
  {
    const abstract_eventt& it_evt=egraph[*it];
    if(
      !(it_evt.variable==var
        &&(it==begin() || it_evt.operation!=abstract_eventt::Read
          || egraph[*prev].operation!=abstract_eventt::Read))
      && it_evt.operation!=abstract_eventt::Fence
      && it_evt.operation!=abstract_eventt::Lwfence
      && it_evt.operation!=abstract_eventt::ASMfence)
      break;
  }

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
  if(size()<=2) return false; //assert(size()>2);

  for(const_iterator it=begin(); it!=end(); ++it)
  {
    const_iterator n_it=it;
    ++n_it;

    if(n_it==end())
      break;

    const abstract_eventt& current=egraph[*it];
    const abstract_eventt& next=egraph[*n_it];

    /* rf */
    if(current.operation==abstract_eventt::Write &&
      next.operation==abstract_eventt::Read)
      continue;

    /* data dependencies */
    const data_dpt& dep=egraph.map_data_dp[current.thread];

    if(dep.dp(current,next))
      continue;

    return true;
  }

  const abstract_eventt& current=egraph[back()];
  const abstract_eventt& next=egraph[front()];

  /* rf */
  if(current.operation == abstract_eventt::Write &&
    next.operation == abstract_eventt::Read)
     return false;

  /* data dependencies */
  const data_dpt& dep=egraph.map_data_dp[current.thread];

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
  for(const_iterator it=begin(); it!=end(); ++it)
    cycle += i2string(egraph[*it].id) + "; ";
  return cycle + " End of cycle.";
}

/*******************************************************************\

Function: event_grapht::critical_cyclet::print_unsafes

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string event_grapht::critical_cyclet::print_unsafes() const
{
  std::string name = "Unsafe pairs: ";
  for(std::set<delayt>::const_iterator it=unsafe_pairs.begin();
    it!=unsafe_pairs.end();
    ++it)
  {
    const abstract_eventt& first=egraph[it->second];
    const abstract_eventt& last=egraph[it->first];

    if(last.variable == first.variable
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
  }

  return name;
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
  for(const_iterator it=begin(); it!=end(); ++it)
  {
    const abstract_eventt& it_evt=egraph[*it];
    cycle += it_evt.get_operation() + id2string(it_evt.variable) 
      + "; ";
  }
  return cycle+" End of cycle.";
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
  for(const_iterator it=begin(); it!=end(); ++it)
  {
    const abstract_eventt& it_evt=egraph[*it];
    cycle += id2string(it_evt.variable) + " ("; 
    cycle += it_evt.location.as_string() + ") ";
  }
  return cycle;
}

/*******************************************************************\

Function: event_grapht::critical_cyclet::print_detail

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string event_grapht::critical_cyclet::print_detail(
  const critical_cyclet& reduced,
  std::map<std::string,std::string>& map_id2var,
  std::map<std::string,std::string>& map_var2id,
  memory_modelt model) const
{
  std::string cycle;
  for(const_iterator it=reduced.begin(); it!=reduced.end(); ++it)
  {
    const abstract_eventt& it_evt=egraph[*it];
    const std::string var_name = id2string(it_evt.variable)
      + " (" + it_evt.location.as_string()  + ")";
    if(map_var2id.find(var_name)!=map_var2id.end())
    {
      cycle += "t" + i2string(it_evt.thread) + " (";
      cycle += map_var2id[var_name] + ") ";
    }
    else
    {
      const std::string new_id = "var@" + i2string(map_var2id.size());
      map_var2id[var_name] = new_id;
      map_id2var[new_id] = var_name;
      cycle += "t" + i2string(it_evt.thread) + " (";
      cycle += new_id + ") ";
    }
  }
  return cycle;
}

/*******************************************************************\

Function: event_grapht::critical_cyclet::print_all

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string event_grapht::critical_cyclet::print_all(
  memory_modelt model,
  std::map<std::string,std::string>& map_id2var,
  std::map<std::string,std::string>& map_var2id,
  bool hide_internals) const
{
  std::string cycle;

  assert(size() > 2);

  /* removes all the internal events */
  if(hide_internals)
  {
    critical_cyclet reduced(egraph, id);
    this->hide_internals(reduced);
    assert(reduced.size() > 0);
    cycle+=print_detail(reduced, map_id2var, map_var2id, model);
    cycle+=": ";
    cycle+=print_name(reduced, model);
  }
  else
  {
    cycle+=print_detail(*this, map_id2var, map_var2id, model);
    cycle+=": ";
    cycle+=print_name(*this, model);
  }

  return cycle;
}

/*******************************************************************\

Function: event_grapht::critical_cyclet::hide_internals

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void event_grapht::critical_cyclet::hide_internals(critical_cyclet& reduced)  const
{
  std::set<unsigned> reduced_evts;
  const_iterator first_it, prev_it=end();

  /* finds an element first of its thread */
  for(first_it=begin(); first_it!=end(); ++first_it)
  {
    const abstract_eventt& first=egraph[*first_it];
    if(prev_it!=end() && egraph[*prev_it].thread!=first.thread
      && !first.is_fence())
      break;
    prev_it=first_it;
  }
  assert(first_it != end());
  reduced.push_back(*first_it);
  reduced_evts.insert(*first_it);

  /* conserves only the extrema of threads */
  for(const_iterator cur_it=first_it; cur_it!=end(); ++cur_it)
  {
    const abstract_eventt& cur=egraph[*cur_it];
    if(cur.is_fence())
      continue;

    const_iterator next_it=cur_it;
    ++next_it;
    if(next_it == end())
      next_it=begin();

    if(cur.thread != egraph[*next_it].thread)
    {
      if(reduced_evts.find(*cur_it) == reduced_evts.end())
      {
        reduced.push_back(*cur_it);
        reduced_evts.insert(*cur_it);
      }
      for(; next_it!=end() && egraph[*next_it].is_fence(); ++next_it);
      assert(next_it != end());
      if(reduced_evts.find(*next_it) == reduced_evts.end())
      {
        reduced.push_back(*next_it);
        reduced_evts.insert(*next_it);
      }
    }
  }

  for(const_iterator cur_it=begin(); cur_it != first_it; ++cur_it)
  {
    const abstract_eventt& cur=egraph[*cur_it];
    if(cur.is_fence())
      continue;

    const_iterator next_it=cur_it;
    ++next_it;
    assert(next_it != end());

    if(cur.thread != egraph[*next_it].thread)
    {
      if(reduced_evts.find(*cur_it)==reduced_evts.end())
      {
        reduced.push_back(*cur_it);
        reduced_evts.insert(*cur_it);
      }
      for(; next_it!=end() && egraph[*next_it].is_fence(); ++next_it);
      assert(next_it != end());
      if(reduced_evts.find(*next_it) == reduced_evts.end())
      {
        reduced.push_back(*next_it);
        reduced_evts.insert(*next_it);
      }
    }
  }
}

/*******************************************************************\

Function: event_grapht::critical_cyclet::print_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string event_grapht::critical_cyclet::print_name(
  const critical_cyclet& reduced,
  memory_modelt model) const
{
  std::string name;
  const_iterator prev_it=reduced.end();
  for(const_iterator cur_it=reduced.begin(); cur_it!=reduced.end(); ++cur_it)
  {
    const abstract_eventt& cur=egraph[*cur_it];

    if(prev_it!=reduced.end())
    {
      const abstract_eventt& prev=egraph[*prev_it];

      if(cur.operation == abstract_eventt::Fence)
      {
        const_iterator n_it=cur_it;
        ++n_it;
        const abstract_eventt& succ=( n_it!=reduced.end() ?
          egraph[*n_it] : egraph[reduced.front()] );
        name += (model==Power?" Sync":" MFence"); 
        name += (prev.variable==cur.variable?"s":"d")
          + prev.get_operation() + succ.get_operation();
      }

      else if(cur.operation == abstract_eventt::Lwfence)
      {
        const_iterator n_it=cur_it;
        ++n_it;
        const abstract_eventt& succ=( n_it!=reduced.end() ?
          egraph[*n_it] : egraph[reduced.front()] );
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

    prev_it=cur_it;
  }

  const abstract_eventt& first=egraph[reduced.front()];
  const abstract_eventt& last=egraph[reduced.back()];

  if(first.operation == abstract_eventt::Fence)
  {
    const_iterator next=reduced.begin();
    ++next;
    const abstract_eventt& succ=egraph[ *next ];
    name += (model==Power?" Sync":" MFence");
    name += (last.variable==first.variable?"s":"d")
      + last.get_operation() + succ.get_operation();
  }

  else if(first.operation == abstract_eventt::Lwfence)
  {
    const_iterator next = reduced.begin();
    ++next;
    const abstract_eventt& succ= egraph[ *next ];
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
  std::ostream &str,
  unsigned colour,
  memory_modelt model) const
{
  /* print vertices */
  for(const_iterator it=begin(); it!=end(); ++it)
  {
    const abstract_eventt& ev=egraph[*it];

    /* id of the cycle in comments */
    str << "/* " << id << " */" << std::endl;

    /* vertex */
    str << ev.id << "[label=\"\\\\lb {" << ev.id << "}" << ev.get_operation();
    str << "{" << ev.variable << "} {} @thread" << ev.thread << "\"];";
    str << std::endl;
  }

  /* print edges */
  const_iterator prev_it=end();
  for(const_iterator cur_it=begin(); cur_it!=end(); ++cur_it)
  {
    const abstract_eventt& cur=egraph[*cur_it];

    /* id of the cycle in comments */
    str << "/* " << id << " */" << std::endl;

    /* edge */
    if(prev_it!=end())
    {
      const abstract_eventt& prev = egraph[*prev_it];

      str << prev.id << "->";
      if(cur.operation == abstract_eventt::Fence)
      {
        const_iterator n_it=cur_it;
        ++n_it;
        const abstract_eventt& succ=( n_it!=end() ?
          egraph[*n_it] : egraph[front()] );
        str << succ.id << "[label=\"";
        str << (model==Power?"Sync":"MFence"); 
        str << (prev.variable==cur.variable?"s":"d");
        str << prev.get_operation() << succ.get_operation();
      }

      else if(cur.operation == abstract_eventt::Lwfence)
      {
        const_iterator n_it=cur_it;
        ++n_it;
        const abstract_eventt& succ=( n_it!=end() ?
          egraph[*n_it] : egraph[front()] );
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

    prev_it=cur_it;
  }

  const abstract_eventt& first=egraph[front()];
  const abstract_eventt& last=egraph[back()];

  /* id of the cycle in comments */
  str << "/* " << id << " */" << std::endl;

  /* edge */
  str << last.id << "->";
  if(first.operation == abstract_eventt::Fence)
  {
    const_iterator next=begin();
    ++next;
    const abstract_eventt& succ=egraph[*next];
    str << succ.id << "[label=\"";
    str << (model==Power?"Sync":"MFence");
    str << (last.variable==first.variable?"s":"d");
    str << last.get_operation() << succ.get_operation();
  }

  else if(first.operation == abstract_eventt::Lwfence)
  {
    const_iterator next=begin();
    ++next;
    const abstract_eventt& succ=egraph[*next];
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
