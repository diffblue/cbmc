/*******************************************************************\

Module: cycles visitor for computing edges involved for fencing

Author: Vincent Nimal

\*******************************************************************/

#include <list>
#include <map>

#include "cycles_visitor.h"
#include "fence_inserter.h"

class instrumentert;

/* implemented: BTWN1, BTWN4 */
#define BTWN1

/*******************************************************************\

Function:

  Inputs:

 Outputs:
 
 Purpose:

\*******************************************************************/

/* po^+ /\ U{C_1, ..., C_n} \/ delays */
void cycles_visitort::po_edges(std::set<unsigned>& edges) 
{
  instrumentert& instrumenter=fence_inserter.instrumenter;

  event_grapht& egraph=instrumenter.egraph;

  for(std::set<event_grapht::critical_cyclet>::iterator
    C_j=instrumenter.set_of_cycles.begin();
    C_j!=instrumenter.set_of_cycles.end();
    ++C_j)
  {
    /* filters */
    if(fence_inserter.filter_cycles(C_j->id))
      continue;

#ifdef BTWN1
    /* btwn1: variables are all the pos involved in cycles, plus the delays
       for dp when analysing Power or ARM */
    if(fence_inserter.model==Power || fence_inserter.model==Unknown) 
    {
      /* for Power/ARM, add also delays as variables for dp (other fences 
         are superfluous if the edge is not in pos; yet it's not harmful) */
      for(std::set<edget>::iterator e_i=C_j->unsafe_pairs.begin();
        e_i!=C_j->unsafe_pairs.end(); ++e_i)
      {
        if(e_i->is_po)
          edges.insert(fence_inserter.add_edge(*e_i));
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
            fence_inserter.const_graph_visitor.const_graph_explore_AC(egraph, 
              next_it->first, new_path);
          }

          for(graph<abstract_eventt>::edgest::const_iterator
            next_it=egraph.po_out(e_i->second).begin();
            next_it!=egraph.po_out(e_i->second).end();
            ++next_it)
          {
            std::list<unsigned> new_path;
            new_path.push_back(e_i->second);
            new_path.push_back(next_it->first);
            fence_inserter.const_graph_visitor.const_graph_explore_BC(egraph, 
              next_it->first, new_path);
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
        edges.insert(fence_inserter.add_edge(e_i));
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
          fence_inserter.const_graph_visitor.const_graph_explore(egraph, 
            next_it->first, e_i.second, new_path);
        }
      }
    }
    /* last case */
    {
      const edget e_i(*cur, C_j->front());

      if(!egraph[*cur].is_fence() && !egraph[C_j->front()].is_fence())
      {
        if(e_i.is_po)
          edges.insert(fence_inserter.add_edge(e_i));
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
            fence_inserter.const_graph_visitor.const_graph_explore(egraph, 
              next_it->first, e_i.second, new_path);
          }
        }
      }
    }
#elif defined BTWN4
    /* add delays as var */
    for(std::set<edget>::iterator e_i=C_j->unsafe_pairs.begin();
      e_i!=C_j->unsafe_pairs.end(); ++e_i)
      edges.insert(fence_inserter.add_edge(*e_i));

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
            fence_inserter.add_edge(edget(c,b));
          else if (egraph.are_po_ordered(a,c) && egraph.are_po_ordered(d,b))
            fence_inserter.add_edge(edget(c,d));
          else if (egraph.are_po_ordered(c,a) && egraph.are_po_ordered(b,d))
            fence_inserter.add_edge(edget(a,b));
          else if (egraph.are_po_ordered(c,a) && egraph.are_po_ordered(d,b))
            fence_inserter.add_edge(edget(a,d));
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
void cycles_visitort::powr_constraint(
  const event_grapht::critical_cyclet& C_j,
  std::set<unsigned>& edges)
{
  event_grapht& graph=fence_inserter.instrumenter.egraph;

  for(std::set<edget>::iterator e_i=C_j.unsafe_pairs.begin();
    e_i!=C_j.unsafe_pairs.end(); ++e_i)
  {
    if(e_i->is_po && (graph[e_i->first].operation==abstract_eventt::Write
        && graph[e_i->second].operation==abstract_eventt::Read))
    {
      if( edges.insert(fence_inserter.add_edge(*e_i)).second )
        ++fence_inserter.constraints_number;
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
void cycles_visitort::poww_constraint(
  const event_grapht::critical_cyclet& C_j,
  std::set<unsigned>& edges)
{
  event_grapht& graph=fence_inserter.instrumenter.egraph;

  for(std::set<edget>::iterator e_i=C_j.unsafe_pairs.begin();
    e_i!=C_j.unsafe_pairs.end(); ++e_i)
  {
    if(e_i->is_po && (graph[e_i->first].operation==abstract_eventt::Write
        && graph[e_i->second].operation==abstract_eventt::Write))
    {
      if( edges.insert(fence_inserter.add_edge(*e_i)).second )
        ++fence_inserter.constraints_number;
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
void cycles_visitort::porw_constraint(
  const event_grapht::critical_cyclet& C_j,
  std::set<unsigned>& edges)
{
  event_grapht& graph=fence_inserter.instrumenter.egraph;

  for(std::set<edget>::iterator e_i=C_j.unsafe_pairs.begin();
    e_i!=C_j.unsafe_pairs.end(); ++e_i)
  {
    if(e_i->is_po && (graph[e_i->first].operation==abstract_eventt::Read
        && graph[e_i->second].operation==abstract_eventt::Write))
    {
      if( edges.insert(fence_inserter.add_edge(*e_i)).second )
        ++fence_inserter.constraints_number;
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
void cycles_visitort::porr_constraint(
  const event_grapht::critical_cyclet& C_j,
  std::set<unsigned>& edges)
{
  event_grapht& graph=fence_inserter.instrumenter.egraph;

  for(std::set<edget>::iterator e_i=C_j.unsafe_pairs.begin();
    e_i!=C_j.unsafe_pairs.end(); ++e_i)
  {
    if(e_i->is_po && (graph[e_i->first].operation==abstract_eventt::Read
        && graph[e_i->second].operation==abstract_eventt::Read))
    {
      if( edges.insert(fence_inserter.add_edge(*e_i)).second )
        ++fence_inserter.constraints_number;
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
void cycles_visitort::com_constraint(
  const event_grapht::critical_cyclet& C_j,                          
  std::set<unsigned>& edges) 
{
  event_grapht& egraph=fence_inserter.instrumenter.egraph;
 
  for(std::set<edget>::const_iterator it=C_j.unsafe_pairs.begin();
    it!=C_j.unsafe_pairs.end();
    ++it)
  {
    if(egraph[it->first].operation==abstract_eventt::Write
      && egraph[it->second].operation==abstract_eventt::Read
      && egraph[it->first].thread!=egraph[it->second].thread)
      if( edges.insert(fence_inserter.add_invisible_edge(*it)).second )
        ++fence_inserter.constraints_number;
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

