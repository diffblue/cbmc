/*******************************************************************\

Module: graph visitor for computing edges involved for fencing

Author: Vincent Nimal

\*******************************************************************/

#include "fence_inserter.h"
#include "graph_visitor.h"

/* implemented: BTWN1, BTWN4 */
#define BTWN1

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void const_graph_visitort::graph_explore(event_grapht& egraph, unsigned next, 
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
      edges.insert(fence_inserter.add_edge(edget(*it,*next_it)));
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

void const_graph_visitort::const_graph_explore(event_grapht& egraph, unsigned next,
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
      fence_inserter.add_edge(edget(*it,*next_it));
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

void const_graph_visitort::graph_explore_BC(event_grapht& egraph, unsigned next,
  std::list<unsigned>& old_path, std::set<unsigned>& edges, bool porw)
{
  /* TODO: restricts to C_1 U ... U C_n for perf improvement */
  assert(old_path.size() > 0);

  fence_inserter.instrumenter.message.debug() << "(BC) explore " << old_path.front() 
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
        edges.insert(fence_inserter.add_edge(edget(*it,*next_it)));
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

void const_graph_visitort::const_graph_explore_BC(event_grapht& egraph, 
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
        fence_inserter.add_edge(edget(*it,*next_it));
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

void const_graph_visitort::graph_explore_AC(event_grapht& egraph, unsigned next,
  std::list<unsigned>& old_path, std::set<unsigned>& edges, bool porw)
{
  /* TODO: restricts to C_1 U ... U C_n */
  assert(old_path.size() > 0);

  fence_inserter.instrumenter.message.debug() << "(AC) explore " 
    << old_path.front() << " --...--> " << next << messaget::eom;

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
        edges.insert(fence_inserter.add_edge(edget(*next_it,*it)));
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

void const_graph_visitort::const_graph_explore_AC(event_grapht& egraph, 
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
        fence_inserter.add_edge(edget(*next_it,*it));
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

void const_graph_visitort::PT(const edget& e, std::set<unsigned>& edges) {
  visited_nodes.clear();

//  if(!e.is_po) /* e is in po^+\po */ is_po is a flag set manually, do not 
//  use it for checks!!
  const graph<abstract_eventt>::edgest& list_po_out=
    fence_inserter.instrumenter.egraph.po_out(e.first);
  if(list_po_out.find(e.second)==list_po_out.end())
  {
#ifdef BTWN1
    event_grapht& egraph=fence_inserter.instrumenter.egraph;

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
    edges.insert(fence_inserter.map_from_e[e]);
}

/*******************************************************************\

Function:

  Inputs: e in comWR /\ C_j (invisible variables)

 Outputs: e's in po /\ C (problem variables)

 Purpose:

\*******************************************************************/

void const_graph_visitort::CT(const edget& edge, std::set<unsigned>& edges) {
  event_grapht& egraph=fence_inserter.instrumenter.egraph;

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

void const_graph_visitort::CT_not_powr(const edget& edge, 
  std::set<unsigned>& edges) 
{
  event_grapht& egraph=fence_inserter.instrumenter.egraph;

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

