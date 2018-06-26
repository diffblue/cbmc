/*******************************************************************\

Module: collection of pairs (for Pensieve's static delay-set
        analysis) in graph of abstract events

Author:

Date: 2013

\*******************************************************************/

/// \file
/// collection of pairs (for Pensieve's static delay-set analysis) in graph of
///   abstract events

#include "event_graph.h"

#include <fstream>

#include <util/message.h>

#define OUTPUT(s, fence, file, line, id, type)  \
  s<<fence<<"|"<<file<<"|"<<line<<"|"<<id<<"|"<<type<<'\n'

void event_grapht::graph_pensieve_explorert::collect_pairs()
{
  std::ofstream res;
  res.open("results.txt");

  for(std::list<event_idt>::const_iterator st_it=egraph.po_order.begin();
    st_it!=egraph.po_order.end(); ++st_it)
  {
    /* pick X */
    event_idt first=*st_it;
    egraph.message.debug() << "first: " << egraph[first].id << messaget::eom;

    if(visited_nodes.find(first)!=visited_nodes.end())
      continue;

    /* by rules (1) + (3), we must have X --cmp-- A */
    if(egraph.com_out(first).empty() && !naive)
      continue;

    /* find Y s.t. X --po-- Y and Y --cmp-- B, by rules (2) + (4) */
    if(find_second_event(first))
    {
      const abstract_eventt &first_event=egraph[first];

      try
      {
        /* directly outputs */
        OUTPUT(res, "fence", first_event.source_location.get_file(),
          first_event.source_location.get_line(), first_event.variable,
            static_cast<int>(first_event.operation));
      }
      catch(const std::string &s)
      {
        egraph.message.warning() << "failed to find" << s << messaget::eom;
        continue;
      }
    }
  }

  res.close();
}

bool event_grapht::graph_pensieve_explorert::find_second_event(
  event_idt current)
{
  if(visited_nodes.find(current)!=visited_nodes.end())
    return false;

  visited_nodes.insert(current);

  for(wmm_grapht::edgest::const_iterator
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
