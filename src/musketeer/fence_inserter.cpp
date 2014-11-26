/*******************************************************************\

Module: ILP construction for all cycles and resolution

Author: Vincent Nimal

\*******************************************************************/

#include <util/i2string.h>
#include <util/graph.h>
#include <goto-instrument/wmm/abstract_event.h>


#ifdef HAVE_GLPK
#include <cstdlib>
#endif

#include "fence_inserter.h"

/* implemented: BTWN1, BTWN4 */
#define BTWN1

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned fence_insertert::fence_cost(fence_typet f) const {
  switch(f) {
    case Fence:
      return 3;
    case Lwfence:
      return 2;
    case Dp:
      return 1;
    case Branching:
      return 2;
    case Ctlfence:
      return 1;     
  }
  assert(false);
  return 0;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_insertert::graph_explore(event_grapht& egraph, unsigned next, 
  unsigned end, std::list<unsigned>& old_path, std::set<unsigned>& edges)
{
  if(next == end) {
    /* inserts all the pos collected from old_path in edges */
    std::list<unsigned>::const_iterator it=old_path.begin();
    std::list<unsigned>::const_iterator next_it=it;
    ++next_it;
    for(;next_it!=old_path.end() && it!=old_path.end(); ++it, ++next_it)
    {
      /* it should be a po_s, and not a po_s^+ */
      assert(egraph.has_po_edge(*it,*next_it));
      edges.insert(add_edge(edget(*it,*next_it)));
    }
  }
  else if(egraph.po_out(next).size()==0) {
    /* this path is not connecting a to b => return */
  }
  else {
    for(graph<abstract_eventt>::edgest::const_iterator
      next_it=egraph.po_out(next).begin();
      next_it!=egraph.po_out(next).end();
      ++next_it)
    {
      if(visited_nodes.find(next_it->first)!=visited_nodes.end())
        continue;
      visited_nodes.insert(next_it->first);

      old_path.push_back/*front*/(next_it->first); 
      graph_explore(egraph, next_it->first, end, old_path, edges);
      old_path.pop_back/*front*/();
    }
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_insertert::const_graph_explore(event_grapht& egraph, unsigned next,
  unsigned end, std::list<unsigned>& old_path)
{
  if(next == end) {
    /* inserts all the pos collected from old_path in edges */
    std::list<unsigned>::const_iterator it=old_path.begin();
    std::list<unsigned>::const_iterator next_it=it;
    ++next_it;
    for(;next_it!=old_path.end() && it!=old_path.end(); ++it, ++next_it)
    {
      /* it should be a po_s, and not a po_s^+ */
      assert(egraph.has_po_edge(*it,*next_it));
      add_edge(edget(*it,*next_it));
    }
  }
  else if(egraph.po_out(next).size()==0) {
    /* this path is not connecting a to b => return */
  }
  else {
    for(graph<abstract_eventt>::edgest::const_iterator
      next_it=egraph.po_out(next).begin();
      next_it!=egraph.po_out(next).end();
      ++next_it)
    {
      if(visited_nodes.find(next_it->first)!=visited_nodes.end())
        continue;
      visited_nodes.insert(next_it->first);

      old_path.push_back/*front*/(next_it->first);
      const_graph_explore(egraph, next_it->first, end, old_path);
      old_path.pop_back/*front*/();
    }
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_insertert::graph_explore_BC(event_grapht& egraph, unsigned next,
  std::list<unsigned>& old_path, std::set<unsigned>& edges, bool porw)
{
  /* TODO: restricts to C_1 U ... U C_n for perf improvement */
  assert(old_path.size() > 0);

  instrumenter.message.debug() << "(BC) explore " << old_path.front() 
    << " --...--> " << next << messaget::eom;

  if(visited_nodes.find(next)!=visited_nodes.end())
     return;
  visited_nodes.insert(next);

  /* if all the incoming pos were already visited, add */
  bool no_other_pos = true;
  for(graph<abstract_eventt>::edgest::const_iterator it=
    egraph.po_out(next).begin();
    it!=egraph.po_out(next).end();
    ++it)
    if(visited_nodes.find(it->first)==visited_nodes.end())
    {
      no_other_pos = false;
      break;
    }

  if(egraph.po_out(next).size()==0 || no_other_pos) {
    /* inserts all the pos collected from old_path in edges */
    std::list<unsigned>::const_iterator it=old_path.begin();
    std::list<unsigned>::const_iterator next_it=it;
    ++next_it;
    for(;next_it!=old_path.end() && it!=old_path.end(); ++it, ++next_it)
    {
      const abstract_eventt& e1=egraph[*it];
      const abstract_eventt& e2=egraph[*next_it];
      if(!porw || (e1.operation==abstract_eventt::Read
        && e2.operation==abstract_eventt::Write))
        edges.insert(add_edge(edget(*it,*next_it)));
    }
    assert(it!=old_path.end());
  }
  else {
    for(graph<abstract_eventt>::edgest::const_iterator
      next_it=egraph.po_out(next).begin();
      next_it!=egraph.po_out(next).end();
      ++next_it)
    {
      old_path.push_back/*front*/(next_it->first);
      graph_explore_BC(egraph, next_it->first, old_path, edges);
      old_path.pop_back/*front*/();
    }
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_insertert::const_graph_explore_BC(event_grapht& egraph, 
  unsigned next, std::list<unsigned>& old_path)
{
  /* TODO: restricts to C_1 U ... U C_n */
  assert(old_path.size() > 0);

  if(visited_nodes.find(next)!=visited_nodes.end())
     return;
  visited_nodes.insert(next);

  /* if all the incoming pos were already visited, add */
  bool no_other_pos = true;
  for(graph<abstract_eventt>::edgest::const_iterator it=
    egraph.po_out(next).begin();
    it!=egraph.po_out(next).end();
    ++it)
    if(visited_nodes.find(it->first)==visited_nodes.end())
    {
      no_other_pos = false;
      break;
    }

  if(egraph.po_out(next).size()==0 || no_other_pos) {
    /* inserts all the pos collected from old_path in edges */
    std::list<unsigned>::const_iterator it=old_path.begin();
    std::list<unsigned>::const_iterator next_it=it;
    ++next_it;
    for(;next_it!=old_path.end() && it!=old_path.end(); ++it, ++next_it)
    {
      const abstract_eventt& e1=egraph[*it];
      const abstract_eventt& e2=egraph[*next_it];
      if((e1.operation==abstract_eventt::Read
        && e2.operation==abstract_eventt::Write))
        add_edge(edget(*it,*next_it));
    }
    // NEW
    assert(it!=old_path.end());
  }
  else {
    for(graph<abstract_eventt>::edgest::const_iterator
      next_it=egraph.po_out(next).begin();
      next_it!=egraph.po_out(next).end();
      ++next_it)
    {
      old_path.push_back/*front*/(next_it->first);
      const_graph_explore_BC(egraph, next_it->first, old_path);
      old_path.pop_back/*front*/();
    }
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_insertert::graph_explore_AC(event_grapht& egraph, unsigned next,
  std::list<unsigned>& old_path, std::set<unsigned>& edges, bool porw)
{
  /* TODO: restricts to C_1 U ... U C_n */
  assert(old_path.size() > 0);

  instrumenter.message.debug() << "(AC) explore " << old_path.front() 
    << " --...--> " << next << messaget::eom;

  if(visited_nodes.find(next)!=visited_nodes.end())
     return;
  visited_nodes.insert(next);

  /* if all the incoming pos were already visited, add */
  bool no_other_pos = true;
  for(graph<abstract_eventt>::edgest::const_iterator it=
    egraph.po_in(next).begin();
    it!=egraph.po_in(next).end();
    ++it)
    if(visited_nodes.find(it->first)==visited_nodes.end())
    {
      no_other_pos = false;
      break;
    }

  if(egraph.po_in(next).size()==0 || no_other_pos) {
    /* inserts all the pos collected from old_path in edges */
    std::list<unsigned>::const_iterator it=old_path.begin();
    std::list<unsigned>::const_iterator next_it=it;
    ++next_it;
    for(;next_it!=old_path.end() && it!=old_path.end(); ++it, ++next_it)
    {
      const abstract_eventt& e1=egraph[*next_it];
      const abstract_eventt& e2=egraph[*it];
      if(!porw || (e1.operation==abstract_eventt::Read 
        && e2.operation==abstract_eventt::Write))
        edges.insert(add_edge(edget(*next_it,*it)));
    }
    assert(it!=old_path.end());
  }
  else {
    for(graph<abstract_eventt>::edgest::const_iterator
      next_it=egraph.po_in(next).begin();
      next_it!=egraph.po_in(next).end();
      ++next_it)
    {
      old_path.push_back/*front*/(next_it->first);
      graph_explore_AC(egraph, next_it->first, old_path, edges);
      old_path.pop_back/*front*/();
    }
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_insertert::const_graph_explore_AC(event_grapht& egraph, 
  unsigned next, std::list<unsigned>& old_path)
{
  /* TODO: restricts to C_1 U ... U C_n */
  assert(old_path.size() > 0);

  if(visited_nodes.find(next)!=visited_nodes.end())
     return;
  visited_nodes.insert(next);

  /* if all the incoming pos were already visited, add */
  bool no_other_pos = true;
  for(graph<abstract_eventt>::edgest::const_iterator it=
    egraph.po_in(next).begin();
    it!=egraph.po_in(next).end();
    ++it)
    if(visited_nodes.find(it->first)==visited_nodes.end())
    {
      no_other_pos = false;
      break;
    }

  /* if beginning of the thread */
  if(egraph.po_in(next).size()==0 || no_other_pos) {
    /* inserts all the pos collected from old_path in edges */
    std::list<unsigned>::const_iterator it=old_path.begin();
    std::list<unsigned>::const_iterator next_it=it;
    ++next_it;
    for(;next_it!=old_path.end() && it!=old_path.end(); ++it, ++next_it)
    {
      const abstract_eventt& e1=egraph[*next_it];
      const abstract_eventt& e2=egraph[*it];
      if((e1.operation==abstract_eventt::Read
        && e2.operation==abstract_eventt::Write))
        add_edge(edget(*next_it,*it));
    }
    // NEW
    assert(it!=old_path.end());
  }
  else {
    for(graph<abstract_eventt>::edgest::const_iterator
      next_it=egraph.po_in(next).begin();
      next_it!=egraph.po_in(next).end();
      ++next_it)
    {
      old_path.push_back/*front*/(next_it->first);
      const_graph_explore_AC(egraph, next_it->first, old_path);
      old_path.pop_back/*front*/();
    }
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_insertert::PT(const edget& e, std::set<unsigned>& edges) {
  visited_nodes.clear();

//  if(!e.is_po) /* e is in po^+\po */ is_po is a flag set manually, do not 
//  use it for checks!!
  const graph<abstract_eventt>::edgest& list_po_out=
    instrumenter.egraph.po_out(e.first);
  if(list_po_out.find(e.second)==list_po_out.end())
  {
#ifdef BTWN1
    event_grapht& egraph=instrumenter.egraph;

    /* all the pos inbetween */
    for(graph<abstract_eventt>::edgest::const_iterator 
      next_it=egraph.po_out(e.first).begin();
      next_it!=egraph.po_out(e.first).end();
      ++next_it)
    {
      std::list<unsigned> new_path;
      new_path.push_back(e.first);
      new_path.push_back(next_it->first);
      graph_explore(egraph, next_it->first, e.second, new_path, edges);
    }
#elif defined BTWN4
    /* all the pos+ intersections inbetween */
    /* TODO */
    /* when detecting intersections, add them to a map thread->edges
       then for BTWN4, enumerates all the edges of the thread of e and
       check whether e.first-po-> edge.first /\ edge.second-po->e.second,
       using egraph.are_po_ordered. */
#else
    throw "BTWN definition not selected!";
#endif
  }
  else
    /* reflexive -- only when in pos */
    edges.insert(map_from_e[e]);
}

/*******************************************************************\

Function:

  Inputs: e in comWR /\ C_j (invisible variables)

 Outputs: e's in po /\ C (problem variables)

 Purpose:

\*******************************************************************/

void fence_insertert::CT(const edget& edge, std::set<unsigned>& edges) {
  event_grapht& egraph=instrumenter.egraph;

  /* the edge can be in the reversed order (back-edge) */
  const abstract_eventt& test_first=egraph[edge.first];
  const abstract_eventt& test_second=egraph[edge.second];
  assert(test_first.operation!=test_second.operation);

  const unsigned first=
    (test_first.operation==abstract_eventt::Write?edge.first:edge.second);
  const unsigned second=
    (test_second.operation==abstract_eventt::Read?edge.second:edge.first);

  /* TODO: AC + restricts to C_1 U ... U C_n */
  visited_nodes.clear();

  /* if one event only on this thread of the cycle, discard */
  if(egraph.po_in(first).size() > 0) 
    for(graph<abstract_eventt>::edgest::const_iterator
      next_it=egraph.po_in(first).begin();
      next_it!=egraph.po_in(first).end();
      ++next_it)
    {
      std::list<unsigned> new_path;
      new_path.push_back(first);
      new_path.push_back(next_it->first);
      graph_explore_AC(egraph, next_it->first, new_path, edges);
    }

  if(egraph.po_out(second).size() > 0)
    for(graph<abstract_eventt>::edgest::const_iterator
      next_it=egraph.po_out(second).begin();
      next_it!=egraph.po_out(second).end();
      ++next_it)
    {
      std::list<unsigned> new_path;
      new_path.push_back(second);
      new_path.push_back(next_it->first);
      graph_explore_BC(egraph, next_it->first, new_path, edges);
    }
}

/*******************************************************************\

Function:

  Inputs: e in comWR /\ C_j (invisible variables)

 Outputs: e's in poRW/\ C (problem variables)

 Purpose:

\*******************************************************************/

void fence_insertert::CT_not_powr(const edget& edge, 
  std::set<unsigned>& edges) 
{
  event_grapht& egraph=instrumenter.egraph;

  /* the edge can be in the reversed order (back-edge) */
  const abstract_eventt& test_first=egraph[edge.first];
  const abstract_eventt& test_second=egraph[edge.second];
  assert(test_first.operation!=test_second.operation);

  const unsigned first=
    (test_first.operation==abstract_eventt::Write?edge.first:edge.second);
  const unsigned second=
    (test_second.operation==abstract_eventt::Read?edge.second:edge.first);
  
  /* TODO: AC + restricts to C_1 U ... U C_n */
  visited_nodes.clear();

  if(egraph.po_in(first).size() > 0)
    for(graph<abstract_eventt>::edgest::const_iterator
      next_it=egraph.po_in(first).begin();
      next_it!=egraph.po_in(first).end();
      ++next_it)
    {
      std::list<unsigned> new_path;
      new_path.push_back(first);
      new_path.push_back(next_it->first);
      graph_explore_AC(egraph, next_it->first, new_path, edges, true);
    }

  if(egraph.po_out(second).size() > 0)
    for(graph<abstract_eventt>::edgest::const_iterator
      next_it=egraph.po_out(second).begin();
      next_it!=egraph.po_out(second).end();
      ++next_it)
    {
      std::list<unsigned> new_path;
      new_path.push_back(second);
      new_path.push_back(next_it->first);
      graph_explore_BC(egraph, next_it->first, new_path, edges, true);
    }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

/* po^+ /\ U{C_1, ..., C_n} \/ delays */
void fence_insertert::po_edges(std::set<unsigned>& edges) {
  for(std::set<event_grapht::critical_cyclet>::iterator
    C_j=instrumenter.set_of_cycles.begin();
    C_j!=instrumenter.set_of_cycles.end();
    ++C_j)
  {
    event_grapht& egraph=instrumenter.egraph;

    /* filters */
    if(filter_cycles(C_j->id))
      continue;

#ifdef BTWN1
    /* btwn1: variables are all the pos involved in cycles, plus the delays
       for dp when analysing Power or ARM */
    if(model==Power || model==Unknown) 
    {
      /* for Power/ARM, add also delays as variables for dp (other fences 
         are superfluous if the edge is not in pos; yet it's not harmful) */
      for(std::set<edget>::iterator e_i=C_j->unsafe_pairs.begin();
        e_i!=C_j->unsafe_pairs.end(); ++e_i)
      {
        if(e_i->is_po)
          edges.insert(add_edge(*e_i));
        else 
        {
          /* also add pos of non-delaying pos+ of cycles, as they could AC or
            BC */
          for(graph<abstract_eventt>::edgest::const_iterator
            next_it=egraph.po_in(e_i->first).begin();
            next_it!=egraph.po_in(e_i->first).end();
            ++next_it)
          {
            std::list<unsigned> new_path;
            new_path.push_back(e_i->first);
            new_path.push_back(next_it->first);
            const_graph_explore_AC(egraph, next_it->first, new_path);
          }

          for(graph<abstract_eventt>::edgest::const_iterator
            next_it=egraph.po_out(e_i->second).begin();
            next_it!=egraph.po_out(e_i->second).end();
            ++next_it)
          {
            std::list<unsigned> new_path;
            new_path.push_back(e_i->second);
            new_path.push_back(next_it->first);
            const_graph_explore_BC(egraph, next_it->first, new_path);
          }
        }
      }
    }

    event_grapht::critical_cyclet::const_iterator cur=C_j->begin();
    assert(cur!=C_j->end());
    event_grapht::critical_cyclet::const_iterator next=cur;
    ++next;
    assert(next!=C_j->end());
    for(; cur!=C_j->end() && next!=C_j->end(); ++cur, ++next)
    {
      if(egraph[*cur].is_fence() || egraph[*next].is_fence())
        continue;

      const edget e_i(*cur, *next);

      if(e_i.is_po)
        edges.insert(add_edge(e_i));
      else
      {
        /* adds basic pos from this pos^+ */
        for(graph<abstract_eventt>::edgest::const_iterator
          next_it=egraph.po_out(e_i.first).begin();
          next_it!=egraph.po_out(e_i.first).end();
          ++next_it)
        {
          std::list<unsigned> new_path;
          new_path.push_back(e_i.first);
          new_path.push_back(next_it->first);
          const_graph_explore(egraph, next_it->first, e_i.second, new_path);
        }
      }
    }
    /* last case */
    {
      const edget e_i(*cur, C_j->front());

      if(!egraph[*cur].is_fence() && !egraph[C_j->front()].is_fence())
      {
        if(e_i.is_po)
          edges.insert(add_edge(e_i));
        else
        {
          /* adds basic pos from this pos^+ */
          for(graph<abstract_eventt>::edgest::const_iterator
            next_it=egraph.po_out(e_i.first).begin();
            next_it!=egraph.po_out(e_i.first).end();
            ++next_it)
          {
            std::list<unsigned> new_path;
            new_path.push_back(e_i.first);
            new_path.push_back(next_it->first);
            const_graph_explore(egraph, next_it->first, e_i.second, new_path);
          }
        }
      }
    }
#elif defined BTWN4
    /* add delays as var */
    for(std::set<edget>::iterator e_i=C_j->unsafe_pairs.begin();
      e_i!=C_j->unsafe_pairs.end(); ++e_i)
      edges.insert(add_edge(*e_i));

    /* maximum pos+ at the intersection of two cycles */
    std::set<event_grapht::critical_cyclet>::iterator C_k=C_j;
    ++C_k;
    for(; C_k!=instrumenter.set_of_cycles.end(); ++C_k)
    {
      /* not necessary; might improve the construction time however */
#if 0
      /* first, let us check if these cycles are entangled */
      event_grapht::critical_cyclet::const_iterator C_j_it=C_j->begin();
      event_grapht::critical_cyclet::const_iterator C_k_it=C_k->begin();
      for(; C_j_it!=C_j->end(); ++C_j_it)
      {
        for(; C_k_it!=C_k->end()
          && !egraph.are_po_ordered(*C_j_it,*C_k_it)
          && !egraph.are_po_ordered(*C_k_it,*C_j_it); ++C_k_it);

        if(C_k_it!=C_k->end())
          break;
      }

      if(C_j_it==C_j->end()) 
        continue;
#endif

      /* computes the largest pos+ in C_j */
      std::map<unsigned,event_grapht::critical_cyclet::const_iterator> m_begin;
      std::map<unsigned,event_grapht::critical_cyclet::const_iterator> m_end;
      std::set<unsigned> m_threads;

      unsigned previous_thread=0;
      for(event_grapht::critical_cyclet::const_iterator C_j_it=C_j->begin();
        C_j_it!=C_j->end(); ++C_j_it)
      {
        const unsigned current_thread=egraph[*C_j_it].thread;

        if(previous_thread==current_thread && C_j_it!=C_j->begin())
          m_end[previous_thread]=C_j_it;
        else
        {
          m_begin[current_thread]=C_j_it;
          m_end[current_thread]=C_j_it;
          m_threads.insert(current_thread);
        }

        previous_thread=current_thread;
      }

      /* computes the largest pos+ in C_k */
      std::map<unsigned,event_grapht::critical_cyclet::const_iterator> k_begin;
      std::map<unsigned,event_grapht::critical_cyclet::const_iterator> k_end;
      std::set<unsigned> k_threads;

      previous_thread=0;
      for(event_grapht::critical_cyclet::const_iterator C_k_it=C_k->begin();
        C_k_it!=C_k->end(); ++C_k_it)
      {
        const unsigned current_thread=egraph[*C_k_it].thread;

        if(previous_thread==current_thread && C_k_it!=C_k->begin())
          k_end[previous_thread]=C_k_it;
        else
        {
          k_begin[current_thread]=C_k_it;
          k_end[current_thread]=C_k_it;
          k_threads.insert(current_thread);
        }

        previous_thread=current_thread;
      }

      /* if there are some commun threads, take the intersection if relevant */
      for(std::set<unsigned>::const_iterator it=m_threads.begin();
        it!=m_threads.end(); ++it)
        if(k_threads.find(*it)!=k_threads.end())
        {
          const unsigned a=*m_begin[*it];
          const unsigned b=*m_end[*it];
          const unsigned c=*k_begin[*it];
          const unsigned d=*k_end[*it];

          if(egraph.are_po_ordered(b,c))
            continue;
          else if (egraph.are_po_ordered(d,a))
            continue;
          else if (egraph.are_po_ordered(a,c) && egraph.are_po_ordered(b,d))
            add_edge(edget(c,b));
          else if (egraph.are_po_ordered(a,c) && egraph.are_po_ordered(d,b))
            add_edge(edget(c,d));
          else if (egraph.are_po_ordered(c,a) && egraph.are_po_ordered(b,d))
            add_edge(edget(a,b));
          else if (egraph.are_po_ordered(c,a) && egraph.are_po_ordered(d,b))
            add_edge(edget(a,d));
        }
    }
#else
    throw "no BTWN definition selected!";
#endif
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

/* C_j /\ po^+ /\ poWR */
void fence_insertert::powr_constraint(
  const event_grapht::critical_cyclet& C_j,
  std::set<unsigned>& edges)
{
  event_grapht& graph=instrumenter.egraph;

  for(std::set<edget>::iterator e_i=C_j.unsafe_pairs.begin();
    e_i!=C_j.unsafe_pairs.end(); ++e_i)
  {
    if(e_i->is_po && (graph[e_i->first].operation==abstract_eventt::Write
        && graph[e_i->second].operation==abstract_eventt::Read))
    {
      if( edges.insert(add_edge(*e_i)).second )
        ++constraints_number;
    }
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

/* C_j /\ po^+ /\ poWW */
void fence_insertert::poww_constraint(
  const event_grapht::critical_cyclet& C_j,
  std::set<unsigned>& edges)
{
  event_grapht& graph=instrumenter.egraph;

  for(std::set<edget>::iterator e_i=C_j.unsafe_pairs.begin();
    e_i!=C_j.unsafe_pairs.end(); ++e_i)
  {
    if(e_i->is_po && (graph[e_i->first].operation==abstract_eventt::Write
        && graph[e_i->second].operation==abstract_eventt::Write))
    {
      if( edges.insert(add_edge(*e_i)).second )
        ++constraints_number;
    }
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

/* C_j /\ po^+ /\ poRW */
void fence_insertert::porw_constraint(
  const event_grapht::critical_cyclet& C_j,
  std::set<unsigned>& edges)
{
  event_grapht& graph=instrumenter.egraph;

  for(std::set<edget>::iterator e_i=C_j.unsafe_pairs.begin();
    e_i!=C_j.unsafe_pairs.end(); ++e_i)
  {
    if(e_i->is_po && (graph[e_i->first].operation==abstract_eventt::Read
        && graph[e_i->second].operation==abstract_eventt::Write))
    {
      if( edges.insert(add_edge(*e_i)).second )
        ++constraints_number;
    }
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

/* C_j /\ po^+ /\ poRR */
void fence_insertert::porr_constraint(
  const event_grapht::critical_cyclet& C_j,
  std::set<unsigned>& edges)
{
  event_grapht& graph=instrumenter.egraph;

  for(std::set<edget>::iterator e_i=C_j.unsafe_pairs.begin();
    e_i!=C_j.unsafe_pairs.end(); ++e_i)
  {
    if(e_i->is_po && (graph[e_i->first].operation==abstract_eventt::Read
        && graph[e_i->second].operation==abstract_eventt::Read))
    {
      if( edges.insert(add_edge(*e_i)).second )
        ++constraints_number;
    }
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

/* C_j /\ comWR */
void fence_insertert::com_constraint(
  const event_grapht::critical_cyclet& C_j,                          
  std::set<unsigned>& edges) 
{
  event_grapht& egraph=instrumenter.egraph;
 
  for(std::set<edget>::const_iterator it=C_j.unsafe_pairs.begin();
    it!=C_j.unsafe_pairs.end();
    ++it)
  {
    if(egraph[it->first].operation==abstract_eventt::Write
      && egraph[it->second].operation==abstract_eventt::Read
      && egraph[it->first].thread!=egraph[it->second].thread)
      if( edges.insert(add_invisible_edge(*it)).second )
        ++constraints_number;
  }

#if 0
  event_grapht& egraph=instrumenter.egraph;

  std::list<unsigned>::const_iterator e_it=C_j.begin();
  std::list<unsigned>::const_iterator next_it=e_it;
  assert(C_j.size()>0);
  ++next_it;
  for(;  next_it!=C_j.end() && e_it!=C_j.end(); ++e_it, ++next_it)
  {
    const abstract_eventt& e1=egraph[*e_it];
    const abstract_eventt& e2=egraph[*next_it];

    if(e1.operation==abstract_eventt::Write 
      && e2.operation==abstract_eventt::Read
      && e1.thread!=e2.thread)
    {
      if( edges.insert(add_invisible_edge(edget(*e_it, *next_it))).second )
        ++constraints_number;
    }
  }
  /* last case */
  assert(e_it!=C_j.end());
  next_it=C_j.begin();

  const abstract_eventt& e1=egraph[*e_it];
  const abstract_eventt& e2=egraph[*next_it];

  if(e1.operation==abstract_eventt::Write 
    && e2.operation==abstract_eventt::Read
    && e1.thread!=e2.thread)
  {
    if( edges.insert(add_invisible_edge(edget(*e_it, *next_it))).second )
      ++constraints_number;
  }
#endif
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_insertert::compute() {
  compute_fence_options();
  instrumenter.message.status() << "Preprocessing" << messaget::eom;
  preprocess();
  instrumenter.message.status() << "Solving" << messaget::eom;
  if(unique>0)
    solve();
  else
    instrumenter.message.result() << "no cycle concerned" << messaget::eom;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_insertert::preprocess() {
  process_cycles_selection();
  po_edges(po);

  /* TODO: replace lists by sets and carefully count the number of constraints
     _with_ removing the existing ones (i.e., those which are not inserted) */

  instrumenter.message.status() << "Preparing cycles" << messaget::eom;
  for(std::set<event_grapht::critical_cyclet>::const_iterator
    C_j=instrumenter.set_of_cycles.begin();
    C_j!=instrumenter.set_of_cycles.end();
    ++C_j)
  {
    /* filtering */
    if(filter_cycles(C_j->id)) 
      continue;

    std::set<unsigned> new_wr_set;
    powr_constraint(*C_j, new_wr_set);
    powr_constraints.push_back(new_wr_set);

    std::set<unsigned> new_ww_set;
    poww_constraint(*C_j, new_ww_set);
    poww_constraints.push_back(new_ww_set);

    std::set<unsigned> new_rw_set;
    porw_constraint(*C_j, new_rw_set);
    porw_constraints.push_back(new_rw_set);

    std::set<unsigned> new_rr_set;
    porr_constraint(*C_j, new_rr_set);
    porr_constraints.push_back(new_rr_set);

    if(model==Power || model==Unknown) {
      std::set<unsigned> new_comset;
      com_constraint(*C_j, new_comset);
      com_constraints.push_back(new_comset);
    }

    assert(powr_constraints.size() == poww_constraints.size());
    assert(poww_constraints.size() == porw_constraints.size());
    assert(porw_constraints.size() == porr_constraints.size());
  }

  // Note: not true if filters
  //assert(non_powr_constraints.size() == instrumenter.set_of_cycles.size());

  // NEW
  /* first, powr constraints: for all C_j */
  for(std::list<std::set<unsigned> >::const_iterator
    e_i=powr_constraints.begin();
    e_i!=powr_constraints.end();
    ++e_i)
  {
    /* for all e */
    for(std::set<unsigned>::const_iterator
      e_c_it=e_i->begin();
      e_c_it!=e_i->end();
      ++e_c_it)
    {
      std::set<unsigned> pt_set;
      assert(map_to_e.find(*e_c_it) != map_to_e.end());
      PT(map_to_e.find(*e_c_it)->second, pt_set);
    }
  }

  /* then, poww constraints: for all C_j */
  for(std::list<std::set<unsigned> >::const_iterator
    e_i=poww_constraints.begin();
    e_i!=poww_constraints.end();
    ++e_i)
  {
    /* for all e */
    for(std::set<unsigned>::const_iterator
      e_nc_it=e_i->begin();
      e_nc_it!=e_i->end();
      ++e_nc_it)
    {
      std::set<unsigned> pt_set;
      assert(map_to_e.find(*e_nc_it) != map_to_e.end());
      PT(map_to_e.find(*e_nc_it)->second, pt_set);
    }
  }

  /* then, porw constraints: for all C_j */
  for(std::list<std::set<unsigned> >::const_iterator
    e_i=porw_constraints.begin();
    e_i!=porw_constraints.end();
    ++e_i)
  {
    /* for all e */
    for(std::set<unsigned>::const_iterator
      e_nc_it=e_i->begin();
      e_nc_it!=e_i->end();
      ++e_nc_it)
    {
      std::set<unsigned> pt_set;
      assert(map_to_e.find(*e_nc_it) != map_to_e.end());
      PT(map_to_e.find(*e_nc_it)->second, pt_set);
    }
  }

  /* then, porr constraints: for all C_j */
  for(std::list<std::set<unsigned> >::const_iterator
    e_i=porr_constraints.begin();
    e_i!=porr_constraints.end();
    ++e_i)
  {
    /* for all e */
    for(std::set<unsigned>::const_iterator
      e_nc_it=e_i->begin();
      e_nc_it!=e_i->end();
      ++e_nc_it)
    {
      std::set<unsigned> pt_set;
      assert(map_to_e.find(*e_nc_it) != map_to_e.end());
      PT(map_to_e.find(*e_nc_it)->second, pt_set);
    }
  }

  if(model==Power || model==Unknown)
  {
    /* finally, Power/ARM constraints for Rfes: for all C_j */
    for(std::list<std::set<unsigned> >::const_iterator
      e_i=com_constraints.begin();
      e_i!=com_constraints.end();
      ++e_i)
    {
      /* for all e */
      for(std::set<unsigned>::const_iterator
        e_c_it=e_i->begin();
        e_c_it!=e_i->end();
        ++e_c_it)
      {
        std::set<unsigned> ct_set;
        assert( invisible_var.map_to_e.find(*e_c_it)
          != invisible_var.map_to_e.end());
        CT(invisible_var.map_to_e.find(*e_c_it)->second, ct_set);

        std::set<unsigned> ct_not_powr_set;
        CT_not_powr(invisible_var.map_to_e.find(*e_c_it)->second,
          ct_not_powr_set);
      }
    }
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void inline fence_insertert::mip_set_var(glp_prob* lp, unsigned& i) {
  glp_add_cols(lp, unique*fence_options);
  //unsigned i=1;
  for(; i<=unique*fence_options; i+=fence_options)
  {
    const bool has_cost = 1; //(po_plus.find(i)==po_plus.end());
    /* has_cost == 0 => invisible variable */
    assert(has_cost); // not useful for this problem

    /* computes the sum of the frequencies of the cycles in which
       this event appears, if requested */
    float freq_sum = 0;
    if(with_freq)
    {
      assert(instrumenter.set_of_cycles.size()==freq_table.size());
      freq_sum += epsilon;
      for(std::set<event_grapht::critical_cyclet>::const_iterator
        C_j=instrumenter.set_of_cycles.begin();
        C_j!=instrumenter.set_of_cycles.end();
        ++C_j)
      {
        /* filters */
        if(filter_cycles(C_j->id)) continue;

        /* if(C_j->find( col_to_var(i) )!=C_j->end()) */
        std::list<unsigned>::const_iterator it;
        for(it = C_j->begin(); it!=C_j->end() && col_to_var(i)!=*it; ++it);

        if(it!=C_j->end())
          freq_sum += freq_table[C_j->id];
      }
    }
    else
      freq_sum = 1;

    if(model==Power || model==Unknown) {
      /* dp variable for e */
      const std::string name_dp="dp_"+i2string(i);
      glp_set_col_name(lp, i, name_dp.c_str());
      glp_set_col_bnds(lp, i, GLP_LO, 0.0, 0.0);
      glp_set_obj_coef(lp, i, (has_cost?fence_cost(Dp):0)*freq_sum);
      glp_set_col_kind(lp, i, GLP_BV);

      /* fence variable for e */
      const std::string name_f="f_"+i2string(i);
      glp_set_col_name(lp, i+1, name_f.c_str());
      glp_set_col_bnds(lp, i+1, GLP_LO, 0.0, 0.0);
      glp_set_obj_coef(lp, i+1, (has_cost?fence_cost(Fence):0)*freq_sum);
      glp_set_col_kind(lp, i+1, GLP_BV);

// Note: uncomment for br and cf fences
#if 0
      /* br variable for e */
      const std::string name_br="br_"+i2string(i);
      glp_set_col_name(lp, i+2, name_br.c_str());
      glp_set_col_bnds(lp, i+2, GLP_LO, 0.0, 0.0);
      glp_set_obj_coef(lp, i+2, (has_cost?fence_cost(Branching):0)*freq_sum);
      glp_set_col_kind(lp, i+2, GLP_BV);

      /* cf variable for e */
      const std::string name_cf="cf_"+i2string(i);
      glp_set_col_name(lp, i+3, name_cf.c_str());
      glp_set_col_bnds(lp, i+3, GLP_LO, 0.0, 0.0);
      glp_set_obj_coef(lp, i+3, (has_cost?fence_cost(Ctlfence):0)*freq_sum);
      glp_set_col_kind(lp, i+3, GLP_BV);
#endif

      if(model==Power) {
        /* lwf variable for e */
        const std::string name_lwf="lwf_"+i2string(i);
        glp_set_col_name(lp, i+2/*4*/, name_lwf.c_str());
        glp_set_col_bnds(lp, i+2/*4*/, GLP_LO, 0.0, 0.0);
        glp_set_obj_coef(lp, i+2/*4*/,
          (has_cost?fence_cost(Lwfence):0)*freq_sum);
        glp_set_col_kind(lp, i+2/*4*/, GLP_BV);
      }
    }
    else {
      /* fence variable for e */
      const std::string name_f="f_"+i2string(i);
      glp_set_col_name(lp, i, name_f.c_str());
      glp_set_col_bnds(lp, i, GLP_LO, 0.0, 0.0);
      glp_set_obj_coef(lp, i, (has_cost?fence_cost(Fence):0)*freq_sum);
      glp_set_col_kind(lp, i, GLP_BV);
    }
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void inline fence_insertert::mip_set_cst(glp_prob* lp, unsigned& i)
{
  glp_add_rows(lp, constraints_number);
  i=1;

  /* first the powr: for all C_j */
  for(
    std::list<std::set<unsigned> >::const_iterator c_wr_it =
      powr_constraints.begin();
    c_wr_it != powr_constraints.end();
    ++c_wr_it)
  {
    /* for all e */
    for(unsigned j=1; j<=c_wr_it->size(); ++j)
    {
      std::string name="C_"+i2string(i)+"_c_wr_"+i2string(j);
      glp_set_row_name(lp, i, name.c_str());
      glp_set_row_bnds(lp, i, GLP_LO, 1.0, 0.0); /* >= 1*/
      ++i;
    }
  }

  /* then the poww: for all C_j */
  for(
    std::list<std::set<unsigned> >::const_iterator c_ww_it =
      poww_constraints.begin();
    c_ww_it != poww_constraints.end();
    ++c_ww_it)
  {
    /* for all e */
    for(unsigned j=1; j<=c_ww_it->size(); ++j)
    {
      std::string name="C_"+i2string(i)+"_c_ww_"+i2string(j);
      glp_set_row_name(lp, i, name.c_str());
      glp_set_row_bnds(lp, i, GLP_LO, 1.0, 0.0); /* >= 1*/
      ++i;
    }
  }

  /* then the porw: for all C_j */
  for(
    std::list<std::set<unsigned> >::const_iterator c_rw_it =
      porw_constraints.begin();
    c_rw_it != porw_constraints.end();
    ++c_rw_it)
  {
    /* for all e */
    for(unsigned j=1; j<=c_rw_it->size(); ++j)
    {
      std::string name="C_"+i2string(i)+"_c_rw_"+i2string(j);
      glp_set_row_name(lp, i, name.c_str());
      glp_set_row_bnds(lp, i, GLP_LO, 1.0, 0.0); /* >= 1*/
      ++i;
    }
  }

  /* and finally the porr: for all C_j */
  for(
    std::list<std::set<unsigned> >::const_iterator c_rr_it =
      porr_constraints.begin();
    c_rr_it != porr_constraints.end();
    ++c_rr_it)
  {
    /* for all e */
    for(unsigned j=1; j<=c_rr_it->size(); ++j)
    {
      std::string name="C_"+i2string(i)+"_c_rr_"+i2string(j);
      glp_set_row_name(lp, i, name.c_str());
      glp_set_row_bnds(lp, i, GLP_LO, 1.0, 0.0); /* >= 1*/
      ++i;
    }
  }

  if(model==Power || model==Unknown) {
    for(
      std::list<std::set<unsigned> >::const_iterator c_it =
        com_constraints.begin();
      c_it != com_constraints.end();
      ++c_it)
    {
      /* for all e */
      for(unsigned j=1; j<=c_it->size(); ++j)
      {
        std::string name="C_"+i2string(i)+"_c_"+i2string(j);
        glp_set_row_name(lp, i, name.c_str());
        glp_set_row_bnds(lp, i, GLP_LO, 1.0, 0.0); /* >= 1*/
        ++i;
      }
    }
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void inline fence_insertert::mip_fill_matrix(glp_prob* lp, unsigned& i,
  int* imat, int* jmat, double* vmat, const unsigned const_constraints_number,
  const unsigned const_unique)
{
  unsigned col=1;
  unsigned row=1;
  i=1;

  /* first, powr constraints: for all C_j */
  for(std::list<std::set<unsigned> >::const_iterator
    e_i=powr_constraints.begin();
    e_i!=powr_constraints.end();
    ++e_i)
  {
    /* for all e */
    for(std::set<unsigned>::const_iterator
      e_c_it=e_i->begin();
      e_c_it!=e_i->end();
      ++e_c_it)
    {
      std::set<unsigned> pt_set;
      assert(map_to_e.find(*e_c_it) != map_to_e.end());
      PT(map_to_e.find(*e_c_it)->second, pt_set);
      /* sum_e' f_e' */
      for(col=1; col<=unique*fence_options; ++col)
      {
        assert(row<=const_constraints_number);
        assert(col<=const_unique*fence_options);
        imat[i]=row;
        jmat[i]=col;
        if(model==Power || model==Unknown) {
          if(pt_set.find(col_to_var(col))!=pt_set.end()
              && col_to_fence(col)==Fence)
            vmat[i]=1.0;
          else
            vmat[i]=0.0;
        }
        else {
          if(pt_set.find(col_to_var(col))!=pt_set.end()
            && col_to_fence(col)==Fence)
            vmat[i]=1.0;
          else
            vmat[i]=0.0;
        }
        ++i;
      }
      ++row;
    }
  }

  /* then, poww constraints: for all C_j */ 
  for(std::list<std::set<unsigned> >::const_iterator
    e_i=poww_constraints.begin();
    e_i!=poww_constraints.end();
    ++e_i)
  {
    /* for all e */
    for(std::set<unsigned>::const_iterator
      e_nc_it=e_i->begin();
      e_nc_it!=e_i->end();
      ++e_nc_it)
    {
      std::set<unsigned> pt_set;
      assert(map_to_e.find(*e_nc_it) != map_to_e.end());
      PT(map_to_e.find(*e_nc_it)->second, pt_set);
      /* sum_e' (f_e' + lwf_e') */
      for(col=1; col<=unique*fence_options; ++col)
      {
        assert(row<=const_constraints_number);
        assert(col<=const_unique*fence_options);
        imat[i]=row;
        jmat[i]=col;
        if(model==Power) {
          if(pt_set.find(col_to_var(col))!=pt_set.end() 
              && (col_to_fence(col)==Lwfence || col_to_fence(col)==Fence))
            vmat[i]=1.0;
          else
            vmat[i]=0.0;
        }
        else {
          if(pt_set.find(col_to_var(col))!=pt_set.end()
            && col_to_fence(col)==Fence)
            vmat[i]=1.0;
          else
            vmat[i]=0.0;
        }
        ++i;
      }
      ++row;
    }
  }

  /* then, porw constraints: for all C_j */
  for(std::list<std::set<unsigned> >::const_iterator
    e_i=porw_constraints.begin();
    e_i!=porw_constraints.end();
    ++e_i)
  {
    /* for all e */
    for(std::set<unsigned>::const_iterator
      e_nc_it=e_i->begin();
      e_nc_it!=e_i->end();
      ++e_nc_it)
    {
      std::set<unsigned> pt_set;
      assert(map_to_e.find(*e_nc_it) != map_to_e.end());
      PT(map_to_e.find(*e_nc_it)->second, pt_set);
      /* dp_e + sum_e' (f_e' + lwf_e' + br_e') */
      for(col=1; col<=unique*fence_options; ++col)
      {
        assert(row<=const_constraints_number);
        assert(col<=const_unique*fence_options);
        imat[i]=row;
        jmat[i]=col;
        if(model==Power) {
          if(col==var_fence_to_col(Dp, *e_nc_it)
              ||(pt_set.find(col_to_var(col))!=pt_set.end()
              && (col_to_fence(col)==Lwfence 
                || col_to_fence(col)==Fence
#if 0
                || col_to_fence(col)==Branching
#endif
              ))
            )
            vmat[i]=1.0;
          else
            vmat[i]=0.0;
        }
        else if (model==Unknown) {
          if(col==var_fence_to_col(Dp, *e_nc_it)
              ||(pt_set.find(col_to_var(col))!=pt_set.end()
              && (col_to_fence(col)==Fence 
#if 0
                || col_to_fence(col)==Branching
#endif
              ))
            )
            vmat[i]=1.0;
          else
            vmat[i]=0.0;
        }
        else {
          if(pt_set.find(col_to_var(col))!=pt_set.end()
            && (col_to_fence(col)==Fence
#if 0
              || col_to_fence(col)==Branching
#endif
            ))
            vmat[i]=1.0;
          else
            vmat[i]=0.0;
        }
        ++i;
      }
      ++row;
    }
  }

  /* then, porr constraints: for all C_j */
  for(std::list<std::set<unsigned> >::const_iterator
    e_i=porr_constraints.begin();
    e_i!=porr_constraints.end();
    ++e_i)
  {
    /* for all e */
    for(std::set<unsigned>::const_iterator
      e_nc_it=e_i->begin();
      e_nc_it!=e_i->end();
      ++e_nc_it)
    {
      std::set<unsigned> pt_set;
      assert(map_to_e.find(*e_nc_it) != map_to_e.end());
      PT(map_to_e.find(*e_nc_it)->second, pt_set);
// uncomment for cf
#if 0
      std::set<unsigned> it_set;
      IT(map_to_e.find(*e_nc_it)->second, it_set);
#endif
      /* dp_e + sum_e' (f_e' + lwf_e') + sum_e'' cf_e'') */
      for(col=1; col<=unique*fence_options; ++col)
      {
        assert(row<=const_constraints_number);
        assert(col<=const_unique*fence_options);
        imat[i]=row;
        jmat[i]=col;
        if(model==Power) {
          if(col==var_fence_to_col(Dp, *e_nc_it)
              ||(pt_set.find(col_to_var(col))!=pt_set.end()
              && (col_to_fence(col)==Lwfence
                || col_to_fence(col)==Fence
              ))
#if 0
              ||(it_set.find(col_to_var(col))!=it_set.end()
              && col_to_fence(col)==Ctlfence)
#endif
            )
            vmat[i]=1.0;
          else
            vmat[i]=0.0;
        }
        else if (model==Unknown) {
          if(col==var_fence_to_col(Dp, *e_nc_it)
              ||(pt_set.find(col_to_var(col))!=pt_set.end()
              && (col_to_fence(col)==Fence
              ))
#if 0
              ||(it_set.find(col_to_var(col))!=it_set.end()
              && col_to_fence(col)==Ctlfence)
#endif   
            )
            vmat[i]=1.0;
          else
            vmat[i]=0.0;
        }
        else {
          if(pt_set.find(col_to_var(col))!=pt_set.end()
            && (col_to_fence(col)==Fence
            ))
            vmat[i]=1.0;
          else
            vmat[i]=0.0;
        }
        ++i;
      }
      ++row;
    }
  }

  if(model==Power || model==Unknown) 
  {
    /* finally, Power/ARM constraints for Rfes: for all C_j */
    for(std::list<std::set<unsigned> >::const_iterator
      e_i=com_constraints.begin();
      e_i!=com_constraints.end();
      ++e_i)
    {
      /* for all e */
      for(std::set<unsigned>::const_iterator
        e_c_it=e_i->begin();
        e_c_it!=e_i->end();
        ++e_c_it)
      {
        unsigned possibilities_met=0;

        std::set<unsigned> ct_set;
        assert( invisible_var.map_to_e.find(*e_c_it)
          != invisible_var.map_to_e.end());
        CT(invisible_var.map_to_e.find(*e_c_it)->second, ct_set);

        std::set<unsigned> ct_not_powr_set;
        CT_not_powr(invisible_var.map_to_e.find(*e_c_it)->second, 
          ct_not_powr_set);

        instrumenter.message.statistics() << "size of CT for " 
          << invisible_var.map_to_e.find(*e_c_it)->second.first << ","
          << invisible_var.map_to_e.find(*e_c_it)->second.second << ": " 
          << ct_set.size() << messaget::eom;

        /* sum_e' f_e' + sum_e'' lwf_e'' */
        for(col=1; col<=unique*fence_options; ++col)
        {
          assert(row<=const_constraints_number);
          assert(col<=const_unique*fence_options);
          imat[i]=row;
          jmat[i]=col;
          if( (ct_set.find(col_to_var(col))!=ct_set.end()
            && col_to_fence(col)==Fence)
            || (ct_not_powr_set.find(col_to_var(col))!=ct_not_powr_set.end()
              && col_to_fence(col)==Lwfence) )
          {
            vmat[i]=1.0;
            ++possibilities_met;
          }
          else
            vmat[i]=0.0;
          ++i;
        }
        ++row;
        assert(possibilities_met);
      }
    }
  }
  instrumenter.message.debug() << "3: " << i << " row: " << row 
    << messaget::eom;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_insertert::solve() {
#ifdef HAVE_GLPK
  glp_prob* lp;
  glp_iocp parm;
  glp_init_iocp(&parm);
  parm.msg_lev=GLP_MSG_OFF;
  parm.presolve=GLP_ON;

  lp=glp_create_prob();
  glp_set_prob_name(lp, "fence optimisation");
  glp_set_obj_dir(lp, GLP_MIN);

  instrumenter.message.statistics() << "po^+ edges considered:"
    << unique << " cycles:" << instrumenter.set_of_cycles.size() 
    << messaget::eom;

  /* sets the variables and coefficients */
  //nb of po+ considered * types of fences (_e)
  unsigned i=1;
  mip_set_var(lp, i);

  /* sets the constraints */
  mip_set_cst(lp, i);

  instrumenter.message.debug() << "3: " << i << messaget::eom;
  assert(i-1==constraints_number);

  const unsigned const_constraints_number=constraints_number;
  const unsigned const_unique=unique;
 
  const unsigned mat_size=const_unique*fence_options*const_constraints_number;
  instrumenter.message.statistics() << "size of the system: " << mat_size
    << messaget::eom;
  instrumenter.message.statistics() << "# of constraints: " 
    << const_constraints_number << messaget::eom;
  instrumenter.message.statistics() << "# of variables: " 
    << const_unique*fence_options << messaget::eom;
  int* imat=(int*)malloc(sizeof(int)*(mat_size+1));
  int* jmat=(int*)malloc(sizeof(int)*(mat_size+1));
  double* vmat=(double*)malloc(sizeof(double)*(mat_size+1));

#ifdef DEBUG
  print_vars();
#endif

  /* fills the constraints coeff */
  /* tables read from 1 in glpk -- first row/column ignored */
  mip_fill_matrix(lp, i, imat, jmat, vmat, const_constraints_number,
    const_unique);

  instrumenter.message.statistics() << "i: " << i << " mat_size: " << mat_size 
    << messaget::eom;
  //assert(i-1==mat_size);

#ifdef DEBUG
  for(i=1; i<=mat_size; ++i)
    instrumenter.message.debug() << i << "[" << imat[i] << "," << jmat[i] 
      << "]=" << vmat[i] << messaget::eom;
#endif

  /* solves MIP by branch-and-cut */
  glp_load_matrix(lp, mat_size, imat, jmat, vmat);
  glp_intopt(lp, &parm);

#ifdef DEBUG
  print_vars();
#endif

  /* checks optimality */
  switch(glp_mip_status(lp)) {
    case GLP_OPT:
      instrumenter.message.result() << "Optimal solution found" 
        << messaget::eom;
      break;
    case GLP_UNDEF:
      instrumenter.message.result() << "Solution undefined" << messaget::eom;
      assert(0);
    case GLP_FEAS:
      instrumenter.message.result() << "Solution feasible, yet not proven \
        optimal, due to early termination" << messaget::eom;
      break;
    case GLP_NOFEAS:
      instrumenter.message.result() 
        << "No feasible solution, the system is UNSAT" << messaget::eom;
      assert(0);
  }

  event_grapht& egraph=instrumenter.egraph;

  /* loads results (x_i) */
  instrumenter.message.statistics() << "minimal cost: " << glp_mip_obj_val(lp) 
    << messaget::eom;
  for(unsigned j=1; j<=const_unique*fence_options; ++j)
  {
    if(glp_mip_col_val(lp, j)>=1)
    {
      /* insert that fence */
      assert(map_to_e.find(col_to_var(j))!=map_to_e.end());
      const edget& delay = map_to_e.find(col_to_var(j))->second;
      instrumenter.message.statistics() << delay.first << " -> " 
        << delay.second << " : " << to_string(col_to_fence(j)) 
        << messaget::eom;
      instrumenter.message.statistics() << "(between " 
        << egraph[delay.first].source_location << " and "
        << egraph[delay.second].source_location << messaget::eom;
      fenced_edges.insert(std::pair<edget,fence_typet>(delay, col_to_fence(j)));
    }
  }

  glp_delete_prob(lp);
  free(imat);
  free(jmat);
  free(vmat);
#else
  throw "Sorry, musketeer requires glpk; please recompile\
    musketeer with glpk.";
#endif
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_insertert::import_freq() {
  /* TODO */
}
