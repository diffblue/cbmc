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
  unified_difft(
    const goto_modelt &model_old,
    const goto_modelt &model_new);

  bool operator()();

  void output(std::ostream &os) const;

  enum class differencet
  {
    SAME,
    DELETED,
    NEW
  };

  using goto_program_difft =
    std::list<std::pair<goto_programt::const_targett, differencet>>;

  void get_diff(
    const irep_idt &function,
    goto_program_difft &dest) const;

protected:
  const goto_functionst &old_goto_functions;
  const namespacet ns_old;
  const goto_functionst &new_goto_functions;
  const namespacet ns_new;

  using differencest = std::vector<differencet>;
  using differences_mapt = std::map<irep_idt, differencest>;

  differences_mapt differences_map;

  void unified_diff(
    const irep_idt &identifier,
    const goto_programt &old_goto_program,
    const goto_programt &new_goto_program);

  void lcss(
    const irep_idt &identifier,
    const goto_programt &old_goto_program,
    const goto_programt &new_goto_program,
    differencest &differences) const;

  void get_diff(
    const irep_idt &identifier,
    const goto_programt &old_goto_program,
    const goto_programt &new_goto_program,
    const differencest &differences,
    goto_program_difft &dest) const;

  void output_diff(
    const irep_idt &identifier,
    const goto_programt &old_goto_program,
    const goto_programt &new_goto_program,
    const differencest &differences,
    std::ostream &os) const;

  bool instructions_equal(
    const goto_programt::instructiont &ins1,
    const goto_programt::instructiont &ins2,
    bool recurse=true) const
  {
    return
      ins1.code==ins2.code &&
      ins1.function==ins2.function &&
      ins1.type==ins2.type &&
      ins1.guard==ins2.guard &&
      ins1.targets.size()==ins2.targets.size() &&
      (ins1.targets.empty() ||
       instructions_equal(
         *ins1.get_target(),
         *ins2.get_target(),
         false));
  }
};

#endif // CPROVER_GOTO_DIFF_UNIFIED_DIFF_H
