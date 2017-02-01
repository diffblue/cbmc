/*******************************************************************\

Module: Function Call Graphs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Function Call Graphs

#ifndef CPROVER_ANALYSES_CALL_GRAPH_H
#define CPROVER_ANALYSES_CALL_GRAPH_H

#include <iosfwd>
#include <map>
#include <unordered_set>

#include <goto-programs/goto_functions.h>

class call_grapht
{
public:
  explicit call_grapht(const goto_functionst &goto_functions) :
    goto_functions(goto_functions) {}

  void operator()();

  void output_dot(std::ostream &out) const;
  void output(std::ostream &out) const;
  void output_xml(std::ostream &out) const;

  typedef std::multimap<irep_idt, irep_idt> grapht;
  grapht graph;

  void add(const irep_idt &caller, const irep_idt &callee);

  void compute_reachable(
    const irep_idt entry_point,
    std::unordered_set<irep_idt, irep_id_hash> &reachable_functions);

protected:
  const goto_functionst &goto_functions;

  void add(const irep_idt &function,
           const goto_programt &body);
};

#endif // CPROVER_ANALYSES_CALL_GRAPH_H
