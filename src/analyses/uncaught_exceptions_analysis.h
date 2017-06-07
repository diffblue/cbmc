/*******************************************************************\

Module: Over-approximative uncaught exceptions analysis

Author: Cristina David

\*******************************************************************/

#ifndef CPROVER_ANALYSES_UNCAUGHT_EXCEPTIONS_ANALYSIS_H
#define CPROVER_ANALYSES_UNCAUGHT_EXCEPTIONS_ANALYSIS_H

#include <algorithm>
#include <map>
#include <set>
#include <goto-programs/goto_functions.h>

/*******************************************************************\

 Class: uncaught_exceptions_domaint

 Purpose: defines the domain used by the uncaught 
          exceptions analysis

\*******************************************************************/

class uncaught_exceptions_analysist;

class uncaught_exceptions_domaint
{
 public:
  void transform(const goto_programt::const_targett,
                 uncaught_exceptions_analysist &,
                 const namespacet &);

  void join(const irep_idt &);
  void join(const std::set<irep_idt> &);

  void make_top()
  {
    thrown.clear();
    stack_caught.clear();
  }

  void get_elements(std::set<irep_idt> &elements);

 private:
  typedef std::vector<std::set<irep_idt>> stack_caughtt;
  stack_caughtt stack_caught;
  std::set<irep_idt> thrown;
};

/*******************************************************************\

 Class: uncaught_exceptions_analysist

 Purpose: computes in exceptions_map an overapproximation of the 
          exceptions thrown by each method

\*******************************************************************/

class uncaught_exceptions_analysist
{
public:
  typedef std::map<irep_idt, std::set<irep_idt>> exceptions_mapt;

  void collect_uncaught_exceptions(
    const goto_functionst &,
    const namespacet &);

  void output(const goto_functionst &);

  void operator()(
    const goto_functionst &,
    const namespacet &,
    exceptions_mapt &);

  friend class uncaught_exceptions_domaint;

 private:
  uncaught_exceptions_domaint domain;
  exceptions_mapt exceptions_map;
};

void uncaught_exceptions(
  const goto_functionst &,
  const namespacet &,
  std::map<irep_idt, std::set<irep_idt>> &);

#endif
