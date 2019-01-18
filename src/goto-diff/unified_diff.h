/*******************************************************************\

Module: Unified diff (using LCSS) of goto functions

Author: Michael Tautschnig

Date: April 2016

\*******************************************************************/

/// \file
/// Unified diff (using LCSS) of goto functions

#ifndef CPROVER_GOTO_DIFF_UNIFIED_DIFF_H
#define CPROVER_GOTO_DIFF_UNIFIED_DIFF_H

#include <iosfwd>
#include <list>
#include <map>
#include <vector>

#include <util/namespace.h>

#include "goto-programs/goto_program.h"

class goto_functionst;
class goto_modelt;
class goto_programt;

class unified_difft
{
public:
  unified_difft(const goto_modelt &model_old, const goto_modelt &model_new);

  bool operator()();

  void output(std::ostream &os) const;

  enum class differencet
  {
    SAME,
    DELETED,
    NEW
  };

  typedef std::list<std::pair<goto_programt::const_targett, differencet>>
    goto_program_difft;

  goto_program_difft get_diff(const irep_idt &function) const;

private:
  const goto_functionst &old_goto_functions;
  const namespacet ns_old;
  const goto_functionst &new_goto_functions;
  const namespacet ns_new;

  typedef std::vector<differencet> differencest;
  typedef std::map<irep_idt, differencest> differences_mapt;

  void unified_diff(
    const irep_idt &identifier,
    const goto_programt &old_goto_program,
    const goto_programt &new_goto_program);

  static differencest lcss(
    const goto_programt &old_goto_program,
    const goto_programt &new_goto_program);

  static goto_program_difft get_diff(
    const goto_programt &old_goto_program,
    const goto_programt &new_goto_program,
    const differencest &differences);

  void output_diff(
    const irep_idt &identifier,
    const goto_programt &old_goto_program,
    const goto_programt &new_goto_program,
    const differencest &differences,
    std::ostream &os) const;

  static bool instructions_equal(
    const goto_programt::instructiont &ins1,
    const goto_programt::instructiont &ins2);

  const differences_mapt &differences_map() const;

  differences_mapt differences_map_;
};

#endif // CPROVER_GOTO_DIFF_UNIFIED_DIFF_H
