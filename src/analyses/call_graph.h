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

#include <goto-programs/goto_functions.h>

class call_grapht
{
public:
  call_grapht();
  explicit call_grapht(const goto_functionst &);

  void output_dot(std::ostream &out) const;
  void output(std::ostream &out) const;
  void output_xml(std::ostream &out) const;

  typedef std::multimap<irep_idt, irep_idt> grapht;
  grapht graph;

  void add(const irep_idt &caller, const irep_idt &callee);
  call_grapht get_inverted() const;

protected:
  void add(const irep_idt &function,
           const goto_programt &body);
};

#endif // CPROVER_ANALYSES_CALL_GRAPH_H
