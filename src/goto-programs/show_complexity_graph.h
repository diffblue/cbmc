/*******************************************************************\

Module: Show the goto functions as a dot program

Author: Benjamin Quiring

\*******************************************************************/

/// \file
/// Show the goto cfg, where nodes are colored based on a
/// "proof complexity" weight mechanism.

#ifndef CPROVER_COMPLEXITY_GRAPH_SHOW_COMPLEXITY_GRAPH
#define CPROVER_COMPLEXITY_GRAPH_SHOW_COMPLEXITY_GRAPH

#include <list>
#include <string>
#include <set>
#include <map>
#include <goto-programs/goto_program.h>
#include "metrics.h"

class namespacet;
class abstract_goto_modelt;
class goto_functionst;
class ui_message_handlert;

// clang-format off
#define OPT_SHOW_COMPLEXITY_GRAPH \
  "(show-complexity-graph)" \
  "(complexity-graph-roots)"

#define HELP_SHOW_COMPLEXITY_GRAPH \
  " --show-complexity-graph        show goto control-flow-graph with nodes colored with proof complexity\n"
// clang-format on

void show_complexity_graph(
  const abstract_goto_modelt &, 
  const std::list<std::string> roots,
  const std::string &path);

void show_complexity_graph(
  const abstract_goto_modelt &, 
  const std::list<std::string> roots,
  const std::string &path,
  const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info);

void show_complexity_graph(
  const abstract_goto_modelt &, 
  const std::list<std::string> roots,
  const std::string &path,
  const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
  const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info);

#endif // CPROVER_COMPLEXITY_GRAPH_SHOW_COMPLEXITY_GRAPH_H
