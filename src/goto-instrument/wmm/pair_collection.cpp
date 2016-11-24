/*******************************************************************\

Module: collection of pairs (for Pensieve's static delay-set 
        analysis) in graph of abstract events

Author:

Date: 2013

\*******************************************************************/

#include <fstream>

#include <util/message.h>

#include "event_graph.h"

#define OUTPUT(s,fence,file,line,id,type)  \
  s<<fence<<"|"<<file<<"|"<<line<<"|"<<id<<"|"<<type<<std::endl

/*******************************************************************\

Function: event_grapht::graph_explorert::collect_pairs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void event_grapht::graph_pensieve_explorert::collect_pairs(namespacet& ns)
{
  std::ofstream res;
  res.open("results.txt");

  for(std::list<unsigned>::const_iterator st_it=egraph.po_order.begin();
    st_it!=egraph.po_order.end(); ++st_it)
  {
    /* pick X */
    unsigned first=*st_it;
    egraph.message.debug() << "first: " << egraph[first].id << messaget::eom;

    if(visited_nodes.find(first)!=visited_nodes.end())
      continue;

    /* by rules (1) + (3), we must have X --cmp-- A */
    if(egraph.com_out(first).empty() && !naive)
      continue;

    /* find Y s.t. X --po-- Y and Y --cmp-- B, by rules (2) + (4) */
    if(find_second_event(first)) 
    {
      const abstract_eventt& first_event=egraph[first];
 
      try {
        /* directly outputs */
        OUTPUT(res, "fence", first_event.source_location.get_file(), 
          first_event.source_location.get_line(), first_event.variable, 
            first_event.operation);
      } catch (std::string s) { 
        egraph.message.warning() << "failed to find" << s << messaget::eom;
        continue; 
      }
    }
  }

  res.close();
}

/*******************************************************************\

Function: event_grapht::graph_explorert::find_second_event

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool event_grapht::graph_pensieve_explorert::find_second_event(
  unsigned current) 
{
  if(visited_nodes.find(current)!=visited_nodes.end())
    return false;

  visited_nodes.insert(current);

  for(graph<abstract_eventt>::edgest::const_iterator
    it=egraph.po_out(current).begin();
    it!=egraph.po_out(current).end(); ++it)
  {
    if(naive || !egraph.com_out(it->first).empty())
      return true;

    if(find_second_event(it->first))
      return true;
  }

  return false;
}

