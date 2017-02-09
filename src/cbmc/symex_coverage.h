/*******************************************************************\

Module: Record and print code coverage of symbolic execution

Author: Michael Tautschnig

Date: March 2016

\*******************************************************************/

#ifndef CPROVER_CBMC_SYMEX_COVERAGE_H
#define CPROVER_CBMC_SYMEX_COVERAGE_H

#include <string>
#include <ostream>
#include <map>

#include <goto-programs/goto_program.h>

class coverage_recordt;
class goto_functionst;
class namespacet;
class xmlt;

class symex_coveraget
{
public:
  explicit symex_coveraget(const namespacet &_ns):ns(_ns)
  {
  }

  void covered(goto_programt::const_targett location)
  {
    std::pair<coveraget::iterator, bool> entry=
      coverage.insert(std::make_pair(location,
                                     coverage_infot(location, 1)));

    if(!entry.second)
      ++(entry.first->second.num_executions);
  }

  bool generate_report(
    const goto_functionst &goto_functions,
    const std::string &path) const;

protected:
  const namespacet &ns;

  struct coverage_infot
  {
    coverage_infot(
      goto_programt::const_targett _location,
      unsigned _num_executions):
      location(_location), num_executions(_num_executions)
    {
    }

    goto_programt::const_targett location;
    unsigned num_executions;
  };

  typedef std::map<goto_programt::const_targett, coverage_infot>
    coveraget;
  coveraget coverage;

  bool output_report(
    const goto_functionst &goto_functions,
    std::ostream &os) const;

  void build_cobertura(
    const goto_functionst &goto_functions,
    xmlt &xml_coverage) const;

  void compute_overall_coverage(
    const goto_functionst &goto_functions,
    coverage_recordt &dest) const;

  friend class goto_program_coverage_recordt;
};

#endif // CPROVER_CBMC_SYMEX_COVERAGE_H
