/*******************************************************************\

Module: graph of abstract events

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

/// \file
/// graph of abstract events

#include "event_graph.h"

#include <util/message.h>

#include <fstream>


#define NB_COLOURS 14
static const char *colour_map[NB_COLOURS]=
  {"red", "blue", "black", "green", "yellow",
  "orange", "blueviolet", "cyan", "cadetblue", "magenta", "palegreen",
  "deeppink", "indigo", "olivedrab"};
#define print_colour(u) colour_map[u%NB_COLOURS]

void event_grapht::print_rec_graph(std::ofstream &file, event_idt node_id,
  std::set<event_idt> &visited)
{
  const abstract_eventt &node=operator[](node_id);
  file << node_id << "[label=\"" << node << ", " << node.source_location <<
    "\"];\n";
  visited.insert(node_id);

  for(wmm_grapht::edgest::const_iterator
    it=po_out(node_id).begin();
    it!=po_out(node_id).end(); ++it)
  {
    file << node_id << "->" << it->first << "[]\n";
    file << "{rank=same; " << node_id << "; " << it->first << "}\n";
    if(visited.find(it->first)==visited.end())
      print_rec_graph(file, it->first, visited);
  }

  for(wmm_grapht::edgest::const_iterator
    it=com_out(node_id).begin();
    it!=com_out(node_id).end(); ++it)
  {
    file << node_id << "->" << it->first << "[style=\"dotted\"]\n";
    if(visited.find(it->first)==visited.end())
      print_rec_graph(file, it->first, visited);
  }
}

void event_grapht::print_graph()
{
  assert(!po_order.empty());
  std::set<event_idt> visited;
  event_idt root=po_order.front();
  std::ofstream file;
  file.open("graph.dot");
  file << "digraph G {\n";
  file << "rankdir=LR;\n";
  print_rec_graph(file, root, visited);
  file << "}\n";
}

/// copies the segment
/// \param begin: top of the subgraph
/// \param explored: set of segments which have already been explored
/// \param end: bottom of the subgraph
void event_grapht::explore_copy_segment(std::set<event_idt> &explored,
  event_idt begin, event_idt end) const
{
  // std::cout << "explores " << begin << " against " << end << '\n';
  if(explored.find(begin)!=explored.end())
    return;

  explored.insert(begin);

  if(begin==end)
    return;

  for(wmm_grapht::edgest::const_iterator it=po_out(begin).begin();
    it!=po_out(begin).end();
    ++it)
    explore_copy_segment(explored, it->first, end);
}

event_idt event_grapht::copy_segment(event_idt begin, event_idt end)
{
  const abstract_eventt &begin_event=operator[](begin);
  const abstract_eventt &end_event=operator[](end);

  /* not sure -- we should allow cross function cycles */
  if(begin_event.source_location.get_file()!=end_event.source_location
    .get_file()
    || begin_event.source_location.get_function()!=end_event.source_location
    .get_function())
    return end;

  if(duplicated_bodies.find(std::make_pair(begin_event, end_event))
    !=duplicated_bodies.end())
    return end;

  duplicated_bodies.insert(std::make_pair(begin_event, end_event));

  message.status() << "tries to duplicate between "
                   << begin_event.source_location
                   << " and " << end_event.source_location << messaget::eom;
  std::set<event_idt> covered;

  /* collects the nodes of the subgraph */
  explore_copy_segment(covered, begin, end);

  if(covered.empty())
    return end;

//  for(std::set<event_idt>::const_iterator it=covered.begin();
//      it!=covered.end(); ++it)
//    std::cout << "covered: " << *it << '\n';

  std::map<event_idt, event_idt> orig2copy;

  /* duplicates nodes */
  for(std::set<event_idt>::const_iterator it=covered.begin();
    it!=covered.end();
    ++it)
  {
    const event_idt new_node=add_node();
    operator[](new_node)(operator[](*it));
    orig2copy[*it]=new_node;
  }

  /* nested loops -- replicates the po_s back-edges */
  // actually not necessary, as they have been treated before
  // (working on back-edges...)

  /* replicates the po_s forward-edges -- O(#E^2) */
  for(std::set<event_idt>::const_iterator it_i=covered.begin();
    it_i!=covered.end();
    ++it_i)
  {
    for(std::set<event_idt>::const_iterator it_j=covered.begin();
      it_j!=covered.end();
      ++it_j)
    {
      /* skips potential back-edges */
      if(*it_j >= *it_i)
        continue;

      if(has_po_edge(*it_j, *it_i))
        add_po_edge(orig2copy[*it_j], orig2copy[*it_i]);
    }
  }

  /* appends the copy to the original, and returns the end of the copy */
  add_po_edge(end, orig2copy[begin]);

  // TODO: to move to goto2graph, after po_s construction
  /* replicates the cmp-edges -- O(#E x #G) */
  for(std::set<event_idt>::const_iterator it_i=covered.begin();
    it_i!=covered.end();
    ++it_i)
  {
    for(event_idt it_j=0;
      it_j<size();
      ++it_j)
    {
      /* skips potential back-edges */
      if(it_j >= *it_i)
        continue;

      if(has_com_edge(it_j, *it_i))
      {
        add_com_edge(it_j, orig2copy[*it_i]);
        add_com_edge(orig2copy[*it_i], it_j);
      }
    }
  }
  // end

  return orig2copy[end];
}

bool event_grapht::critical_cyclet::check_AC(
  const_iterator s_it,
  const abstract_eventt &first,
  const abstract_eventt &second) const
{
  bool AC=false;
  const_iterator AC_it=s_it;
  ++AC_it;
  for(; AC_it!=end(); ++AC_it)
  {
    const abstract_eventt &AC_evt=egraph[*AC_it];
    if(AC_evt.operation==abstract_eventt::operationt::Fence)
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
  {
    for(AC_it=begin(); ; ++AC_it)
    {
      const abstract_eventt &AC_evt=egraph[*AC_it];
      if(AC_evt.operation==abstract_eventt::operationt::Fence)
      {
        AC=true;
        break;
      }
      if(AC_evt==first || AC_evt.thread!=second.thread)
        break;
    }
  }

  return AC;
}

bool event_grapht::critical_cyclet::check_BC(
  const_iterator it,
  const abstract_eventt &first,
  const abstract_eventt &second) const
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
    const abstract_eventt &BC_evt=egraph[*BC_it];
    if(BC_evt.operation==abstract_eventt::operationt::Fence)
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
      const abstract_eventt &BC_evt=egraph[*BC_it];
      if(BC_evt.operation==abstract_eventt::operationt::Fence)
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

bool event_grapht::critical_cyclet::is_unsafe(memory_modelt model, bool fast)
{
  egraph.message.debug() << "cycle is safe?" << messaget::eom;
  bool unsafe_met=false;

  /* critical cycles contain at least 4 events */
  if(size()<4)
    return false;

  /* critical cycles contain at least 2 threads */
  unsigned thread=egraph[*begin()].thread;
  const_iterator th_it;
  for(th_it=begin();
    th_it!=end() && thread==egraph[*th_it].thread; ++th_it)
    thread=egraph[*th_it].thread;
  if(th_it==end())
    return false;

  /* selects the first element of the pair */
  const_iterator it=begin();
  const_iterator next=it;
  ++next;
  for(; it!=end() && next!=end(); ++next, ++it)
  {
    const abstract_eventt &it_evt=egraph[*it];
    const abstract_eventt &next_evt=egraph[*next];

    /* strong fence -- this pair is safe */
    if(it_evt.operation==abstract_eventt::operationt::Fence)
      continue;

    if(next_evt.operation==abstract_eventt::operationt::Fence)
      continue;

    /* first element is a weak fence */
    if(it_evt.operation==abstract_eventt::operationt::Lwfence)
      continue;

    /* selects the next event which is not a weak fence */
    const_iterator s_it=next;

    for(; s_it!=end() &&
          egraph[*s_it].operation==abstract_eventt::operationt::Lwfence;
        ++s_it)
    {
    }

    if(s_it==end())
      continue;

    const abstract_eventt &s_evt=egraph[*s_it];

    if(s_evt.operation==abstract_eventt::operationt::Fence)
      continue;

    /* if the whole cycle has been explored */
    if(it==s_it)
      continue;

    const abstract_eventt &first=it_evt;
    const abstract_eventt &second=s_evt;
    const data_dpt &data_dp=egraph.map_data_dp[first.thread];

    /* if data dp between linking the pair, safe */
    if(first.thread==second.thread && data_dp.dp(first, second))
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
      if(first.unsafe_pair(second, model)
        && (first.thread!=second.thread || egraph.are_po_ordered(*it, *s_it)))
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

        if(first.variable==second.variable
          && first.thread==second.thread
          && egraph[*before_first].thread!=first.thread
          && egraph[*after_second].thread!=second.thread)
        {
          /* not unsafe */
        }
        else
        {
          if(fast)
            return true;
          else
          {
            const delayt delay(*it, *s_it, (first.thread==second.thread));
            unsafe_pairs.insert(delay);
            unsafe_met=true;
          }
        }
      }
    }
    else
    {
      /* one (or more) lwfence between the pair */
      if(first.unsafe_pair_lwfence(second, model)
        && (first.thread!=second.thread || egraph.are_po_ordered(*it, *s_it)))
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

        if(first.variable==second.variable
          && first.thread==second.thread
          && egraph[*before_first].thread!=first.thread
          && egraph[*after_second].thread!=second.thread)
        {
          /* not unsafe */
        }
        else
        {
          if(fast)
            return true;
          else
          {
            const delayt delay(*it, *s_it, (first.thread==second.thread));
            unsafe_pairs.insert(delay);
            unsafe_met=true;
          }
        }
      }
    }
  }

  /* strong fence -- this pair is safe */
  if(egraph[back()].operation==abstract_eventt::operationt::Fence
    || egraph[front()].operation==abstract_eventt::operationt::Fence)
    return unsafe_met;

  /* first element is a weak fence */
  if(egraph[back()].operation==abstract_eventt::operationt::Lwfence)
    return unsafe_met;

  /* selects the next event which is not a weak fence */
  const_iterator s_it;
  for(s_it=begin();
      s_it!=end() &&
      egraph[*s_it].operation==abstract_eventt::operationt::Lwfence;
      s_it++)
  {
  }

  /* if the whole cycle has been explored */
  if(s_it==end())
    return unsafe_met;

  if(egraph[*s_it].operation==abstract_eventt::operationt::Fence)
    return unsafe_met;

  const abstract_eventt &first=egraph[back()];
  const abstract_eventt &second=egraph[*s_it];

  const data_dpt &data_dp=egraph.map_data_dp[first.thread];

  /* if data dp between linking the pair, safe */
  if(first.thread==second.thread && data_dp.dp(first, second))
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
    if(first.unsafe_pair(second, model)
      && (first.thread!=second.thread || egraph.are_po_ordered(back(), *s_it)))
    {
      std::list<event_idt>::const_iterator before_first;
      std::list<event_idt>::const_iterator after_second;

      before_first=end();
      --before_first;
      --before_first;

      after_second=s_it;
      ++after_second;

      if(first.variable==second.variable
        && first.thread==second.thread
        && egraph[*before_first].thread!=first.thread
        && egraph[*after_second].thread!=second.thread)
      {
        /* not unsafe */
      }
      else
      {
        if(!fast)
        {
          const delayt delay(back(), *s_it, (first.thread==second.thread));
          unsafe_pairs.insert(delay);
        }
        return true;
      }
    }
  }
  else
  {
    /* one (or more) lwfence between the pair */
    if(first.unsafe_pair_lwfence(second, model)
      && (first.thread!=second.thread || egraph.are_po_ordered(back(), *s_it)))
    {
      std::list<event_idt>::const_iterator before_first;
      std::list<event_idt>::const_iterator after_second;

      before_first=end();
      --before_first;
      --before_first;

      after_second=s_it;
      ++after_second;

      if(first.variable==second.variable
        && first.thread==second.thread
        && egraph[*before_first].thread!=first.thread
        && egraph[*after_second].thread!=second.thread)
      {
        /* not unsafe */
      }
      else
      {
        if(!fast)
        {
          const delayt delay(back(), *s_it, (first.thread==second.thread));
          unsafe_pairs.insert(delay);
        }
      return true;
      }
    }
  }

  return unsafe_met;
}

/// same as is_unsafe, but with ASM fences
bool event_grapht::critical_cyclet::is_unsafe_asm(
  memory_modelt model,
  bool fast)
{
  egraph.message.debug() << "cycle is safe?" << messaget::eom;
  bool unsafe_met=false;
  unsigned char fences_met=0;

  /* critical cycles contain at least 4 events */
  if(size()<4)
    return false;

  /* critical cycles contain at least 2 threads */
  unsigned thread=egraph[*begin()].thread;
  const_iterator th_it;
  for(th_it=begin();
    th_it!=end() && thread==egraph[*th_it].thread; ++th_it)
    thread=egraph[*th_it].thread;
  if(th_it==end())
    return false;

  /* selects the first element of the pair */
  for(const_iterator it=begin(); it!=end() && ++it!=end(); it++)
  {
    --it;
    fences_met=0;

    /* fence -- this pair is safe */
    if(egraph[*it].operation==abstract_eventt::operationt::ASMfence)
      continue;

    if(egraph[*(++it)].operation==abstract_eventt::operationt::ASMfence)
    {
      --it;
      continue;
    }

    --it;

    /* selects the next event which is not a weak fence */
    const_iterator s_it=++it;
    --it;

    for(;
      s_it!=end() &&
      egraph[*s_it].operation==abstract_eventt::operationt::ASMfence;
      s_it++)
      fences_met |= egraph[*s_it].fence_value();

    if(s_it==end())
      continue;

    if(egraph[*s_it].operation==abstract_eventt::operationt::ASMfence)
      continue;

    /* if the whole cycle has been explored */
    if(it==s_it)
      continue;

    const abstract_eventt &first=egraph[*it];
    const abstract_eventt &second=egraph[*s_it];

    const data_dpt &data_dp=egraph.map_data_dp[first.thread];

    /* if data dp between linking the pair, safe */
    if(first.thread==second.thread && data_dp.dp(first, second))
      continue;

    /* AC and BC conditions */
    if(first.thread!=second.thread && model==Power)
    {
      bool AC=false;
      bool BC=false;

      /* no fence after the second element? (AC) */
      const_iterator AC_it=++s_it;
      --s_it;
      for(;
        AC_it!=end() && egraph[*AC_it].thread==second.thread;
        AC_it++)
        if(egraph[*AC_it].operation==abstract_eventt::operationt::ASMfence
          && egraph[*AC_it].is_cumul()
          && egraph[*AC_it].is_corresponding_fence(egraph[*it], egraph[*s_it]))
        {
          AC=true;
          break;
        }

      if(AC)
        continue;

      if(AC_it==end() && egraph[front()].thread==second.thread)
      {
        for(AC_it=begin();
            !(egraph[*AC_it]==first) && egraph[*AC_it].thread==second.thread;
            AC_it++)
          if(egraph[*AC_it].operation==abstract_eventt::operationt::ASMfence &&
             egraph[*AC_it].is_cumul() &&
             egraph[*AC_it].is_corresponding_fence(egraph[*it], egraph[*s_it]))
          {
            AC=true;
            break;
          }
      }

      if(AC)
        continue;

      /* no fence before the first element? (BC) */
      const_iterator BC_it;
      if(it==begin())
      {
        BC_it=end();
        BC_it--;
      }
      else
      {
        BC_it=--it;
        ++it;
      }
      for( ;
          BC_it!=begin() && egraph[*BC_it].thread==first.thread;
          BC_it--)
      {
        if(egraph[*BC_it].operation==abstract_eventt::operationt::ASMfence &&
           egraph[*BC_it].is_cumul() &&
           egraph[*BC_it].is_corresponding_fence(egraph[*it], egraph[*s_it]))
        {
          BC=true;
          break;
        }
      }

      if(BC)
        continue;

      if(BC_it==begin() && egraph[back()].thread==first.thread)
      {
        for(BC_it=end();
            !(egraph[*BC_it]==second) && egraph[*BC_it].thread==first.thread;
            BC_it--)
          if(egraph[*BC_it].operation==abstract_eventt::operationt::ASMfence &&
             egraph[*BC_it].is_cumul() &&
             egraph[*BC_it].is_corresponding_fence(egraph[*it], egraph[*s_it]))
          {
            BC=true;
            break;
          }
      }

      if(BC)
        continue;
    }

    if(s_it==++it)
    {
      --it;

      /* no lwfence between the pair */
      if(first.unsafe_pair(second, model)
        && (first.thread!=second.thread || egraph.are_po_ordered(*it, *s_it)))
      {
        if(fast)
          return true;
        else
        {
          const delayt delay(*it, *s_it, (first.thread==second.thread));
          unsafe_pairs.insert(delay);
          unsafe_met=true;
        }
      }
    }
    else
    {
      --it;

      /* one (or more) lwfence between the pair */
      if(first.unsafe_pair_asm(second, model, fences_met)
        && (first.thread!=second.thread || egraph.are_po_ordered(*it, *s_it)))
      {
        if(fast)
          return true;
        else
        {
          const delayt delay(*it, *s_it, (first.thread==second.thread));
          unsafe_pairs.insert(delay);
          unsafe_met=true;
        }
      }
    }
  }

  /* strong fence -- this pair is safe */
  if(egraph[back()].operation==abstract_eventt::operationt::ASMfence
    || egraph[front()].operation==abstract_eventt::operationt::ASMfence)
    return unsafe_met;

  fences_met=0;

  /* selects the next event which is not a weak fence */
  const_iterator s_it;
  for(s_it=begin();
    s_it!=end() &&
    egraph[*s_it].operation==abstract_eventt::operationt::ASMfence;
    s_it++)
    fences_met |= egraph[*s_it].fence_value();

  /* if the whole cycle has been explored */
  if(s_it==end())
    return unsafe_met;

  if(egraph[*s_it].operation==abstract_eventt::operationt::ASMfence)
    return unsafe_met;

  const abstract_eventt &first=egraph[back()];
  const abstract_eventt &second=egraph[*s_it];

  const data_dpt &data_dp=egraph.map_data_dp[first.thread];

  /* if data dp between linking the pair, safe */
  if(first.thread==second.thread && data_dp.dp(first, second))
    return unsafe_met;

  /* AC and BC conditions */
  if(first.thread!=second.thread && model==Power)
  {
    bool AC=false;
    bool BC=false;

    /* no fence after the second element? (AC) */
    const_iterator AC_it=++s_it;
    --s_it;
    for(;
      AC_it!=end() && egraph[*AC_it].thread==second.thread;
      AC_it++)
      if(egraph[*AC_it].operation==abstract_eventt::operationt::ASMfence
        && egraph[*AC_it].is_cumul()
        && egraph[*AC_it].is_corresponding_fence(first, second))
      {
        AC=true;
        break;
      }

    if(AC)
      return unsafe_met;

    if(AC_it==end() && egraph[front()].thread==second.thread)
    {
      for(AC_it=begin();
          !(egraph[*AC_it]==first) && egraph[*AC_it].thread==second.thread;
          AC_it++)
        if(egraph[*AC_it].operation==abstract_eventt::operationt::ASMfence &&
           egraph[*AC_it].is_cumul() &&
           egraph[*AC_it].is_corresponding_fence(first, second))
        {
          AC=true;
          break;
        }
    }

    if(AC)
      return unsafe_met;

    /* no fence before the first element? (BC) */
    const_iterator BC_it=end();
    --BC_it;

    for(;
      BC_it!=begin() && egraph[*BC_it].thread==first.thread;
      BC_it--)
      if(egraph[*BC_it].operation==abstract_eventt::operationt::ASMfence
        && egraph[*BC_it].is_cumul()
        && egraph[*BC_it].is_corresponding_fence(first, second))
      {
        BC=true;
        break;
      }

    if(BC)
      return unsafe_met;

    if(BC_it==begin() && egraph[back()].thread==first.thread)
    {
      BC_it=end();
      BC_it--;
      for(;
        !(egraph[*BC_it]==second) && egraph[*BC_it].thread==first.thread;
        BC_it--)
        if(egraph[*BC_it].operation==abstract_eventt::operationt::ASMfence
          && egraph[*BC_it].is_cumul()
          && egraph[*BC_it].is_corresponding_fence(first, second))
        {
          BC=true;
          break;
        }
    }

    if(BC)
      return unsafe_met;
  }

  if(s_it==begin())
  {
    /* no lwfence between the pair */
    if(first.unsafe_pair(second, model)
      && (first.thread!=second.thread || egraph.are_po_ordered(back(), *s_it)))
    {
      if(!fast)
      {
        const delayt delay(back(), *s_it, (first.thread==second.thread));
        unsafe_pairs.insert(delay);
      }
      return true;
    }
  }
  else
  {
    /* one (or more) lwfence between the pair */
    if(first.unsafe_pair_asm(second, model, fences_met)
      && (first.thread!=second.thread || egraph.are_po_ordered(back(), *s_it)))
    {
      if(!fast)
      {
        const delayt delay(back(), *s_it, (first.thread==second.thread));
        unsafe_pairs.insert(delay);
      }
      return true;
    }
  }

  return unsafe_met;
}

bool event_grapht::critical_cyclet::is_not_uniproc() const
{
  const_iterator it=begin();

  /* find the first non-fence event */
  for(; it!=end(); ++it)
  {
    const abstract_eventt &it_evt=egraph[*it];
    if(it_evt.operation!=abstract_eventt::operationt::Fence
      && it_evt.operation!=abstract_eventt::operationt::Lwfence
      && it_evt.operation!=abstract_eventt::operationt::ASMfence)
      break;
  }

  /* if only fences, uniproc */
  if(it==end())
    return false;

  const irep_idt &var=egraph[*it].variable;

  /* if it is an array access, by over-approximation, we don't have
     uniproc in the cycle (tab[]) */
  if(!egraph.ignore_arrays && id2string(var).find("[]")!=std::string::npos)
    return true;

  for(; it!=end(); ++it)
  {
    const abstract_eventt &it_evt=egraph[*it];
    if(it_evt.variable!=var
      && it_evt.operation!=abstract_eventt::operationt::Fence
      && it_evt.operation!=abstract_eventt::operationt::Lwfence
      && it_evt.operation!=abstract_eventt::operationt::ASMfence)
      break;
  }

  return (it!=end());
}

bool event_grapht::critical_cyclet::is_not_weak_uniproc() const
{
  const_iterator it=begin();

  /* find the first non-fence event */
  for(; it!=end(); it++)
  {
    const abstract_eventt &it_evt=egraph[*it];
    if(it_evt.operation!=abstract_eventt::operationt::Fence
      && it_evt.operation!=abstract_eventt::operationt::Lwfence
      && it_evt.operation!=abstract_eventt::operationt::ASMfence)
      break;
  }

  /* if only fences, uniproc */
  if(it==end())
    return false;

  const irep_idt &var=egraph[*it].variable;

  const_iterator prev=it;
  for(; it!=end(); prev=it, ++it)
  {
    const abstract_eventt &it_evt=egraph[*it];
    if(
      !(it_evt.variable==var
        &&(it==begin() || it_evt.operation!=abstract_eventt::operationt::Read
          || egraph[*prev].operation!=abstract_eventt::operationt::Read))
      && it_evt.operation!=abstract_eventt::operationt::Fence
      && it_evt.operation!=abstract_eventt::operationt::Lwfence
      && it_evt.operation!=abstract_eventt::operationt::ASMfence)
      break;
  }

  return (it!=end());
}

bool event_grapht::critical_cyclet::is_not_thin_air() const
{
  // assert(size()>2);
  if(size()<=2)
    return false;

  for(const_iterator it=begin(); it!=end(); ++it)
  {
    const_iterator n_it=it;
    ++n_it;

    if(n_it==end())
      break;

    const abstract_eventt &current=egraph[*it];
    const abstract_eventt &next=egraph[*n_it];

    /* rf */
    if(current.operation==abstract_eventt::operationt::Write &&
      next.operation==abstract_eventt::operationt::Read)
      continue;

    /* data dependencies */
    const data_dpt &dep=egraph.map_data_dp[current.thread];

    if(dep.dp(current, next))
      continue;

    return true;
  }

  const abstract_eventt &current=egraph[back()];
  const abstract_eventt &next=egraph[front()];

  /* rf */
  if(current.operation==abstract_eventt::operationt::Write &&
    next.operation==abstract_eventt::operationt::Read)
     return false;

  /* data dependencies */
  const data_dpt &dep=egraph.map_data_dp[current.thread];

  if(dep.dp(current, next))
    return false;

  return true;
}

std::string event_grapht::critical_cyclet::print() const
{
  std::string cycle="Cycle: ";
  for(const_iterator it=begin(); it!=end(); ++it)
    cycle += std::to_string(egraph[*it].id) + "; ";
  return cycle + " End of cycle.";
}

std::string event_grapht::critical_cyclet::print_unsafes() const
{
  std::string name="Unsafe pairs: ";
  for(std::set<delayt>::const_iterator it=unsafe_pairs.begin();
    it!=unsafe_pairs.end();
    ++it)
  {
    const abstract_eventt &first=egraph[it->second];
    const abstract_eventt &last=egraph[it->first];

    if(last.variable==first.variable
      && last.operation==abstract_eventt::operationt::Write
      && first.operation==abstract_eventt::operationt::Read)
    {
      name += " Rf";
      name += (last.thread==first.thread?"i":"e");
    }

    else if(last.variable==first.variable &&
            last.operation==abstract_eventt::operationt::Read &&
            first.operation==abstract_eventt::operationt::Write &&
            (last.thread!=first.thread || it->first > it->second))
    {
      name += " Fr";
      name += (last.thread==first.thread?"i":"e");
    }
    else if(last.variable==first.variable &&
            last.operation==abstract_eventt::operationt::Write &&
            first.operation==abstract_eventt::operationt::Write &&
            (last.thread!=first.thread || it->first > it->second))
    {
      /* we prefer to write Po rather than Wsi */
      name += " Ws";
      name += (last.thread==first.thread?"i":"e");
    }
    else if(last.thread==first.thread &&
            last.operation!=abstract_eventt::operationt::Fence)
    {
      name += " Po";
      name += (last.variable==first.variable?"s":"d") + last.get_operation()
        + first.get_operation();
    }
  }

  return name;
}

std::string event_grapht::critical_cyclet::print_events() const
{
  std::string cycle="Cycle: ";
  for(const_iterator it=begin(); it!=end(); ++it)
  {
    const abstract_eventt &it_evt=egraph[*it];
    cycle += it_evt.get_operation() + id2string(it_evt.variable)
      + "; ";
  }
  return cycle+" End of cycle.";
}

std::string event_grapht::critical_cyclet::print_output() const
{
  std::string cycle;
  for(const_iterator it=begin(); it!=end(); ++it)
  {
    const abstract_eventt &it_evt=egraph[*it];
    cycle += id2string(it_evt.variable) + " (";
    cycle += it_evt.source_location.as_string();
    cycle += " thread " + std::to_string(it_evt.thread) + ") ";
  }
  return cycle;
}

std::string event_grapht::critical_cyclet::print_detail(
  const critical_cyclet &reduced,
  std::map<std::string, std::string> &map_id2var,
  std::map<std::string, std::string> &map_var2id) const
{
  std::string cycle;
  for(const_iterator it=reduced.begin(); it!=reduced.end(); ++it)
  {
    const abstract_eventt &it_evt=egraph[*it];
    const std::string var_name=id2string(it_evt.variable)
      + " (" + it_evt.source_location.as_string()  + ")";
    if(map_var2id.find(var_name)!=map_var2id.end())
    {
      cycle += "t" + std::to_string(it_evt.thread) + " (";
      cycle += map_var2id[var_name] + ") ";
    }
    else
    {
      const std::string new_id="var@" + std::to_string(map_var2id.size());
      map_var2id[var_name]=new_id;
      map_id2var[new_id]=var_name;
      cycle += "t" + std::to_string(it_evt.thread) + " (";
      cycle += new_id + ") ";
    }
  }
  return cycle;
}

std::string event_grapht::critical_cyclet::print_all(
  memory_modelt model,
  std::map<std::string, std::string> &map_id2var,
  std::map<std::string, std::string> &map_var2id,
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
    cycle+=print_detail(reduced, map_id2var, map_var2id);
    cycle+=": ";
    cycle+=print_name(reduced, model);
  }
  else
  {
    cycle+=print_detail(*this, map_id2var, map_var2id);
    cycle+=": ";
    cycle+=print_name(*this, model);
  }

  return cycle;
}

void event_grapht::critical_cyclet::hide_internals(
  critical_cyclet &reduced)  const
{
  std::set<event_idt> reduced_evts;
  const_iterator first_it, prev_it=end();

  /* finds an element first of its thread */
  for(first_it=begin(); first_it!=end(); ++first_it)
  {
    const abstract_eventt &first=egraph[*first_it];
    if(prev_it!=end() && egraph[*prev_it].thread!=first.thread
      && !first.is_fence())
      break;
    prev_it=first_it;
  }
  assert(first_it!=end());
  reduced.push_back(*first_it);
  reduced_evts.insert(*first_it);

  /* conserves only the extrema of threads */
  for(const_iterator cur_it=first_it; cur_it!=end(); ++cur_it)
  {
    const abstract_eventt &cur=egraph[*cur_it];
    if(cur.is_fence())
      continue;

    const_iterator next_it=cur_it;
    ++next_it;
    if(next_it==end())
      next_it=begin();

    if(cur.thread!=egraph[*next_it].thread)
    {
      if(reduced_evts.find(*cur_it)==reduced_evts.end())
      {
        reduced.push_back(*cur_it);
        reduced_evts.insert(*cur_it);
      }
      for(; next_it!=end() && egraph[*next_it].is_fence(); ++next_it) {}
      assert(next_it!=end());
      if(reduced_evts.find(*next_it)==reduced_evts.end())
      {
        reduced.push_back(*next_it);
        reduced_evts.insert(*next_it);
      }
    }
  }

  for(const_iterator cur_it=begin(); cur_it!=first_it; ++cur_it)
  {
    const abstract_eventt &cur=egraph[*cur_it];
    if(cur.is_fence())
      continue;

    const_iterator next_it=cur_it;
    ++next_it;
    assert(next_it!=end());

    if(cur.thread!=egraph[*next_it].thread)
    {
      if(reduced_evts.find(*cur_it)==reduced_evts.end())
      {
        reduced.push_back(*cur_it);
        reduced_evts.insert(*cur_it);
      }
      for(; next_it!=end() && egraph[*next_it].is_fence(); ++next_it) {}
      assert(next_it!=end());
      if(reduced_evts.find(*next_it)==reduced_evts.end())
      {
        reduced.push_back(*next_it);
        reduced_evts.insert(*next_it);
      }
    }
  }
}

std::string event_grapht::critical_cyclet::print_name(
  const critical_cyclet &reduced,
  memory_modelt model) const
{
  assert(reduced.size()>=2);
  unsigned extra_fence_count=0;

  std::string name;
  const_iterator prev_it=reduced.end();
  bool first_done=false;
  for(const_iterator cur_it=reduced.begin(); cur_it!=reduced.end(); ++cur_it)
  {
    const abstract_eventt &cur=egraph[*cur_it];

    if(prev_it!=reduced.end())
    {
      const abstract_eventt &prev=egraph[*prev_it];

      if(prev.operation==abstract_eventt::operationt::Fence ||
         prev.operation==abstract_eventt::operationt::Lwfence ||
         prev.operation==abstract_eventt::operationt::ASMfence)
      {
        ++extra_fence_count;
        // nothing to do
      }

      else if(cur.operation==abstract_eventt::operationt::Fence)
      {
        const_iterator n_it=cur_it;
        bool wraparound=false;
        while(true)
        {
          ++n_it;
          if(n_it==reduced.end())
          {
            assert(!wraparound);
            wraparound=true;
            first_done=true;
            ++extra_fence_count;
            n_it=reduced.begin();
          }
          const abstract_eventt &cand=egraph[*n_it];
          if(cand.operation!=abstract_eventt::operationt::Fence &&
             cand.operation!=abstract_eventt::operationt::Lwfence &&
             cand.operation!=abstract_eventt::operationt::ASMfence)
            break;
          if(!wraparound)
            ++cur_it;
          if(!wraparound)
            ++extra_fence_count;
        }
        const abstract_eventt &succ=egraph[*n_it];
        assert(succ.operation==abstract_eventt::operationt::Read ||
               succ.operation==abstract_eventt::operationt::Write);
        name += (model==Power?" Sync":" MFence");
        name += (prev.variable==succ.variable?"s":"d")
          + prev.get_operation() + succ.get_operation();
      }

      else if(cur.operation==abstract_eventt::operationt::Lwfence)
      {
        std::string cand_name=" LwSync";
        const_iterator n_it=cur_it;
        bool wraparound=false;
        while(true)
        {
          ++n_it;
          if(n_it==reduced.end())
          {
            assert(!wraparound);
            wraparound=true;
            first_done=true;
            ++extra_fence_count;
            n_it=reduced.begin();
          }
          const abstract_eventt &cand=egraph[*n_it];
          if(cand.operation!=abstract_eventt::operationt::Fence &&
             cand.operation!=abstract_eventt::operationt::Lwfence &&
             cand.operation!=abstract_eventt::operationt::ASMfence)
            break;
          else if(cand.operation==abstract_eventt::operationt::Fence ||
                  (cand.operation==abstract_eventt::operationt::ASMfence &&
                   cand.fence_value()&1))
            cand_name=(model==Power?" Sync":" MFence");
          if(!wraparound)
            ++cur_it;
          if(!wraparound)
            ++extra_fence_count;
        }
        const abstract_eventt &succ=egraph[*n_it];
        assert(succ.operation==abstract_eventt::operationt::Read ||
               succ.operation==abstract_eventt::operationt::Write);
        name += cand_name;
        name += (prev.variable==succ.variable?"s":"d")
          + prev.get_operation() + succ.get_operation();
      }

      else if(cur.operation==abstract_eventt::operationt::ASMfence)
      {
        std::string cand_name;
        if(cur.fence_value()&1)
          cand_name=(model==Power?" Sync":" MFence");
        else
          cand_name=" LwSync";
        const_iterator n_it=cur_it;
        bool wraparound=false;
        while(true)
        {
          ++n_it;
          if(n_it==reduced.end())
          {
            assert(!wraparound);
            wraparound=true;
            first_done=true;
            ++extra_fence_count;
            n_it=reduced.begin();
          }
          const abstract_eventt &cand=egraph[*n_it];
          if(cand.operation!=abstract_eventt::operationt::Fence &&
             cand.operation!=abstract_eventt::operationt::Lwfence &&
             cand.operation!=abstract_eventt::operationt::ASMfence)
            break;
          else if(cand.operation==abstract_eventt::operationt::Fence ||
                  (cand.operation==abstract_eventt::operationt::ASMfence &&
                   cand.fence_value()&1))
            cand_name=(model==Power?" Sync":" MFence");
          if(!wraparound)
            ++cur_it;
          if(!wraparound)
            ++extra_fence_count;
        }
        const abstract_eventt &succ=egraph[*n_it];
        assert(succ.operation==abstract_eventt::operationt::Read ||
               succ.operation==abstract_eventt::operationt::Write);
        name += cand_name;
        name += (prev.variable==succ.variable?"s":"d")
          + prev.get_operation() + succ.get_operation();
      }

      else if(prev.variable==cur.variable
        && prev.operation==abstract_eventt::operationt::Write
        && cur.operation==abstract_eventt::operationt::Read)
      {
        name += " Rf";
        name += (prev.thread==cur.thread?"i":"e");
      }

      else if(prev.variable==cur.variable
        && prev.operation==abstract_eventt::operationt::Read
        && cur.operation==abstract_eventt::operationt::Write
        && (prev.thread!=cur.thread || *prev_it > *cur_it))
      {
        name += " Fr";
        name += (prev.thread==cur.thread?"i":"e");
      }

      else if(prev.variable==cur.variable &&
              prev.operation==abstract_eventt::operationt::Write &&
              cur.operation==abstract_eventt::operationt::Write &&
              (prev.thread!=cur.thread || *prev_it > *cur_it))
      {
        /* we prefer to write Po rather than Wsi */
        name += " Ws";
        name += (prev.thread==cur.thread?"i":"e");
      }

      else if(prev.thread==cur.thread
        && prev.operation!=abstract_eventt::operationt::Fence
        && prev.operation!=abstract_eventt::operationt::Lwfence
        && prev.operation!=abstract_eventt::operationt::ASMfence)
      {
        const data_dpt &dep=egraph.map_data_dp[cur.thread];

        if(prev.operation==abstract_eventt::operationt::Read &&
           dep.dp(prev, cur))
        {
          name += " DpData";
          name += (prev.variable==cur.variable?"s":"d")
            + cur.get_operation();
        }
        else
        {
          name += " Po";
          name += (prev.variable==cur.variable?"s":"d") + prev.get_operation()
            + cur.get_operation();
        }
      }

      else if(cur.variable!=ID_unknown && prev.variable!=ID_unknown)
        assert(false);
    }

    prev_it=cur_it;
  }

  if(first_done)
  {
    auto n_events=extra_fence_count;
    for(std::string::const_iterator it=name.begin();
        it!=name.end();
        ++it)
      if(*it==' ')
        ++n_events;
    assert(n_events==reduced.size());

    return name;
  }

  const abstract_eventt &first=egraph[reduced.front()];
  const abstract_eventt &last=egraph[reduced.back()];

  assert(last.operation!=abstract_eventt::operationt::Fence &&
         last.operation!=abstract_eventt::operationt::Lwfence &&
         last.operation!=abstract_eventt::operationt::ASMfence);

  if(first.operation==abstract_eventt::operationt::Fence ||
     first.operation==abstract_eventt::operationt::Lwfence ||
     first.operation==abstract_eventt::operationt::ASMfence)
  {
    std::string cand_name=" LwSync";
    const_iterator it=reduced.begin();
    for( ; it!=reduced.end(); ++it)
    {
      const abstract_eventt &cand=egraph[*it];

      if(cand.operation!=abstract_eventt::operationt::Fence &&
         cand.operation!=abstract_eventt::operationt::Lwfence &&
         cand.operation!=abstract_eventt::operationt::ASMfence)
        break;
      else if(cand.operation==abstract_eventt::operationt::Fence ||
              (cand.operation==abstract_eventt::operationt::ASMfence &&
               cand.fence_value()&1))
        cand_name=(model==Power?" Sync":" MFence");
    }
    assert(it!=reduced.begin() && it!=reduced.end());
    const abstract_eventt &succ=egraph[*it];
    assert(succ.operation==abstract_eventt::operationt::Read ||
           succ.operation==abstract_eventt::operationt::Write);
    name += cand_name;
    name += (last.variable==succ.variable?"s":"d")
      + last.get_operation() + succ.get_operation();
  }

  else if(last.variable==first.variable
    && last.operation==abstract_eventt::operationt::Write
    && first.operation==abstract_eventt::operationt::Read)
  {
    name += " Rf";
    name += (last.thread==first.thread?"i":"e");
  }

  else if(last.variable==first.variable
    && last.operation==abstract_eventt::operationt::Read
    && first.operation==abstract_eventt::operationt::Write
    && (last.thread!=first.thread || reduced.back() > reduced.front()))
  {
    name += " Fr";
    name += (last.thread==first.thread?"i":"e");
  }

  else if(last.variable==first.variable &&
          last.operation==abstract_eventt::operationt::Write &&
          first.operation==abstract_eventt::operationt::Write &&
          (last.thread!=first.thread || reduced.back() > reduced.front()))
  {
    /* we prefer to write Po rather than Wsi */
    name += " Ws";
    name += (last.thread==first.thread?"i":"e");
  }

  else if(last.thread==first.thread)
  {
    const data_dpt &dep=egraph.map_data_dp[last.thread];

    if(last.operation==abstract_eventt::operationt::Read &&
       dep.dp(last, first))
    {
      name += " DpData";
      name += (last.variable==first.variable?"s":"d")
        + first.get_operation();
    }
    else
    {
      name += " Po";
      name += (last.variable==first.variable?"s":"d") + last.get_operation()
        + first.get_operation();
    }
  }

  else if(last.variable!=ID_unknown && first.variable!=ID_unknown)
    assert(false);

#if 0
  critical_cyclet::size_type n_events=extra_fence_count;
  for(std::string::const_iterator it=name.begin();
      it!=name.end();
      ++it)
    if(*it==' ')
      ++n_events;
  assert(n_events==reduced.size());
#endif

  return name;
}

void event_grapht::critical_cyclet::print_dot(
  std::ostream &str,
  unsigned colour,
  memory_modelt model) const
{
  /* print vertices */
  for(const_iterator it=begin(); it!=end(); ++it)
  {
    const abstract_eventt &ev=egraph[*it];

    /* id of the cycle in comments */
    str << "/* " << id << " */\n";

    /* vertex */
    str << ev.id << "[label=\"\\\\lb {" << ev.id << "}" << ev.get_operation();
    str << "{" << ev.variable << "} {} @thread" << ev.thread << "\"];\n";
  }

  /* print edges */
  const_iterator prev_it=end();
  for(const_iterator cur_it=begin(); cur_it!=end(); ++cur_it)
  {
    const abstract_eventt &cur=egraph[*cur_it];

    /* id of the cycle in comments */
    str << "/* " << id << " */\n";

    /* edge */
    if(prev_it!=end())
    {
      const abstract_eventt &prev=egraph[*prev_it];

      str << prev.id << "->";
      if(cur.operation==abstract_eventt::operationt::Fence)
      {
        const_iterator n_it=cur_it;
        ++n_it;
        const abstract_eventt &succ=
          n_it!=end() ? egraph[*n_it] : egraph[front()];
        str << succ.id << "[label=\"";
        str << (model==Power?"Sync":"MFence");
        str << (prev.variable==cur.variable?"s":"d");
        str << prev.get_operation() << succ.get_operation();
      }
      else if(cur.operation==abstract_eventt::operationt::Lwfence)
      {
        const_iterator n_it=cur_it;
        ++n_it;
        const abstract_eventt &succ=
          n_it!=end() ? egraph[*n_it] : egraph[front()];
        str << succ.id << "[label=\"";
        str << "LwSync" << (prev.variable==cur.variable?"s":"d");
        str  <<prev.get_operation() << succ.get_operation();
      }
      else if(prev.variable==cur.variable
        && prev.operation==abstract_eventt::operationt::Write
        && cur.operation==abstract_eventt::operationt::Read)
      {
        str << cur.id << "[label=\"";
        str << "Rf" << (prev.thread==cur.thread?"i":"e");
      }
      else if(prev.variable==cur.variable
        && prev.operation==abstract_eventt::operationt::Read
        && cur.operation==abstract_eventt::operationt::Write)
      {
        str << cur.id << "[label=\"";
        str << "Fr" << (prev.thread==cur.thread?"i":"e");
      }
      else if(prev.variable==cur.variable &&
              prev.operation==abstract_eventt::operationt::Write &&
              cur.operation==abstract_eventt::operationt::Write &&
              prev.thread!=cur.thread)
      {
        /* we prefer to write Po rather than Wsi */
        str << cur.id << "[label=\"";
        str << "Ws" << (prev.thread==cur.thread?"i":"e");
      }
      else if(prev.thread==cur.thread &&
              prev.operation!=abstract_eventt::operationt::Fence)
      {
        str << cur.id << "[label=\"";
        str << "Po" << (prev.variable==cur.variable?"s":"d")
          + prev.get_operation() + cur.get_operation();
      }
      else
        str << cur.id << "[label=\"?";

      str << "\",color=" << print_colour(colour) << "];\n";
    }

    prev_it=cur_it;
  }

  const abstract_eventt &first=egraph[front()];
  const abstract_eventt &last=egraph[back()];

  /* id of the cycle in comments */
  str << "/* " << id << " */\n";

  /* edge */
  str << last.id << "->";
  if(first.operation==abstract_eventt::operationt::Fence)
  {
    const_iterator next=begin();
    ++next;
    const abstract_eventt &succ=egraph[*next];
    str << succ.id << "[label=\"";
    str << (model==Power?"Sync":"MFence");
    str << (last.variable==first.variable?"s":"d");
    str << last.get_operation() << succ.get_operation();
  }
  else if(first.operation==abstract_eventt::operationt::Lwfence)
  {
    const_iterator next=begin();
    ++next;
    const abstract_eventt &succ=egraph[*next];
    str << succ.id << "[label=\"";
    str << "LwSync" << (last.variable==first.variable?"s":"d");
    str << last.get_operation() << succ.get_operation();
  }
  else if(last.variable==first.variable &&
          last.operation==abstract_eventt::operationt::Write &&
          first.operation==abstract_eventt::operationt::Read)
  {
    str << first.id << "[label=\"";
    str << "Rf" << (last.thread==first.thread?"i":"e");
  }
  else if(last.variable==first.variable &&
          last.operation==abstract_eventt::operationt::Read &&
          first.operation==abstract_eventt::operationt::Write)
  {
    str << first.id << "[label=\"";
    str << "Fr" << (last.thread==first.thread?"i":"e");
  }
  else if(last.variable==first.variable &&
          last.operation==abstract_eventt::operationt::Write &&
          first.operation==abstract_eventt::operationt::Write &&
          last.thread!=first.thread)
  {
    /* we prefer to write Po rather than Wsi */
    str << first.id << "[label=\"";
    str << "Ws" << (last.thread==first.thread?"i":"e");
  }
  else if(last.thread==first.thread &&
          last.operation!=abstract_eventt::operationt::Fence)
  {
    str << first.id << "[label=\"";
    str << "Po" << (last.variable==first.variable?"s":"d");
    str << last.get_operation() << first.get_operation();
  }
  else
    str << first.id << "[label=\"?";

  str << "\", color=" << print_colour(colour) << "];\n";
}
