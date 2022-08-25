/*******************************************************************\

Module: Show the complexity call graph as a dot program

Author: Benjamin Quiring

\*******************************************************************/

/// \file
/// Show the complexity call graph, where nodes are colored based on a
/// "proof complexity" weight mechanism and have annotations describing
/// the features of different functions.

#ifndef CPROVER_COMPLEXITY_GRAPH_SHOW_COMPLEXITY_GRAPH
#define CPROVER_COMPLEXITY_GRAPH_SHOW_COMPLEXITY_GRAPH

#include <list>
#include <string>
#include <set>
#include <map>
#include <goto-programs/goto_program.h>
#include "metrics.h"
#include <util/options.h>
#include <util/ui_message.h>

class abstract_goto_modelt;
class ui_message_handlert;

// clang-format off

// flags usable by both goto-instrument and CBMC
#define HELP_SHOW_COMPLEXITY_GRAPH \
  " --show-complexity-graph        show call graph with nodes colored with proof complexity\n" \
  " --complexity-graph-root        provides a root for the complexity graph. TODO\n" \
  " --complexity-graph-omit-function   omits a function from the complexity graph\n" \
  " --complexity-graph-omit-function-pointers   omits function pointers from the complexity graph\n" \
  " --complexity-graph-global-scores   uses a globalized notion of complexity for the complexity graph\n"

// flags only usable with CBMC
#define HELP_SHOW_COMPLEXITY_GRAPH_CBMC \
  "--show-complexity-graph-with-symex     show the complexity graph and include symbolic execution information \n" \
  "--show-complexity-graph-with-solver     show the complexity graph and include symbolic execution and solver formula information \n" \
  "--complexity-graph-instructions     display which GOTO instructions were complex for symbolic execution and generating the solver formula\n"

// flags usable by both goto-instrument and CBMC
#define OPT_COMPLEXITY_GRAPH \
  "(show-complexity-graph)" \
  "(complexity-graph-root):" \
  "(complexity-graph-omit-function):" \
  "(complexity-graph-omit-function-pointers)" \
  "(complexity-graph-global-scores)"

// flags only usable with CBMC
#define OPT_COMPLEXITY_GRAPH_CBMC \
  "(show-complexity-graph-with-symex):" \
  "(show-complexity-graph-with-solver):" \
  "(complexity-graph-instructions)"

// clang-format on

void show_complexity_graph(
  const optionst &options,
  const abstract_goto_modelt &,
  const std::string &path,
  message_handlert &message_handler);

void show_complexity_graph(
  const optionst &options,
  const abstract_goto_modelt &,
  const std::string &path,
  message_handlert &message_handler,
  const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info);

void show_complexity_graph(
  const optionst &options,
  const abstract_goto_modelt &,
  const std::string &path,
  message_handlert &message_handler,
  const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info,
  const std::map<goto_programt::const_targett, solver_infot> &instr_solver_info);

#endif // CPROVER_COMPLEXITY_GRAPH_SHOW_COMPLEXITY_GRAPH_H
