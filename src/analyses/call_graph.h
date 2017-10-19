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

#include <goto-programs/goto_model.h>

class call_grapht
{
public:
  explicit call_grapht(bool collect_callsites=false);
  explicit call_grapht(const goto_modelt &, bool collect_callsites=false);
  explicit call_grapht(const goto_functionst &, bool collect_callsites=false);

  void output_dot(std::ostream &out) const;
  void output(std::ostream &out) const;
  void output_xml(std::ostream &out) const;

  typedef std::multimap<irep_idt, irep_idt> grapht;
  typedef std::pair<irep_idt, irep_idt> edget;
  typedef goto_programt::const_targett locationt;
  typedef std::set<locationt> locationst;
  typedef std::map<edget, locationst> callsitest;

  grapht graph;
  callsitest callsites;

  void add(const irep_idt &caller, const irep_idt &callee);
  void add(const irep_idt &caller, const irep_idt &callee, locationt callsite);
  call_grapht get_inverted() const;

protected:
  void add(const irep_idt &function,
           const goto_programt &body);
private:
  bool collect_callsites;
  std::string format_callsites(const edget &edge) const;
};

#endif // CPROVER_ANALYSES_CALL_GRAPH_H
