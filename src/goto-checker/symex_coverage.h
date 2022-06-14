/*******************************************************************\

Module: Record and print code coverage of symbolic execution

Author: Michael Tautschnig

Date: March 2016

\*******************************************************************/

/// \file
/// Record and print code coverage of symbolic execution

#ifndef CPROVER_CBMC_SYMEX_COVERAGE_H
#define CPROVER_CBMC_SYMEX_COVERAGE_H

#include <iosfwd>
#include <map>
#include <string>

#include <goto-programs/goto_program.h>

class coverage_recordt;
class goto_functionst;
class namespacet;
class xmlt;

class symex_coveraget
{
public:
  explicit symex_coveraget(const namespacet &_ns) : ns(_ns)
  {
  }

  void
  covered(goto_programt::const_targett from, goto_programt::const_targett to, double duration)
  {
    std::pair<coverage_innert::iterator, bool> entry =
      coverage[from].insert({to, coverage_infot(from, to, 1, duration)});

    if(!entry.second) {
      ++(entry.first->second.num_executions);
      entry.first->second.duration += duration;
    }
  }

  bool generate_report(
    const goto_functionst &goto_functions,
    const std::string &path) const;

  const goto_programt::const_targetst coverage_to (goto_programt::const_targett from) const;
  const int num_executions (goto_programt::const_targett from, goto_programt::const_targett to) const;
  const double duration (goto_programt::const_targett from, goto_programt::const_targett to) const;

protected:
  const namespacet &ns;

  struct coverage_infot
  {
    coverage_infot(
      goto_programt::const_targett _from,
      goto_programt::const_targett _to,
      unsigned _num_executions,
      double _duration)
      : location(_from), num_executions(_num_executions), succ(_to), duration(_duration)
    {
    }

    goto_programt::const_targett location;
    unsigned num_executions;
    goto_programt::const_targett succ;
    double duration;
  };

  typedef std::map<goto_programt::const_targett, coverage_infot>
    coverage_innert;
  typedef std::map<goto_programt::const_targett, coverage_innert> coveraget;
  coveraget coverage;

  bool
  output_report(const goto_functionst &goto_functions, std::ostream &os) const;

  void build_cobertura(
    const goto_functionst &goto_functions,
    xmlt &xml_coverage) const;

  void compute_overall_coverage(
    const goto_functionst &goto_functions,
    coverage_recordt &dest) const;

  friend class goto_program_coverage_recordt;
};

#endif // CPROVER_CBMC_SYMEX_COVERAGE_H
