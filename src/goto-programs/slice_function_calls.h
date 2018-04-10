/*******************************************************************\

Module: Slice Function Calls and Direct Dependency Parameters

Author: Matthias Güdemann, matthias.guedemann@diffblue.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_SLICE_FUNCTION_CALLS_H
#define CPROVER_GOTO_PROGRAMS_SLICE_FUNCTION_CALLS_H

#include <regex>
#include <string>

#include <util/graph.h>

#include "goto_model.h"

void slice_function_calls(goto_functiont &, const std::string &);
void slice_function_calls(goto_modelt &, const std::string &);

/// Enumeration identifying the type of node in dependency graph
enum class slice_node_typet
{
  FUNCTION_PARAMETER,
  LOCAL_VARIABLE,
  FUNCTION_CALL,
  OTHER
};

/// Node type for dependency graph
struct slice_nodet : public graph_nodet<empty_edget>
{
  slice_node_typet slice_node_type;
  irep_idt name;
  unsigned location_number = 0;
  // node index in dependency graph
  node_indext node_index;
};

typedef grapht<slice_nodet> slice_function_grapht;
typedef std::list<slice_nodet> slice_nodest;

/// Class to remove selected function calls from a GOTO program in
/// JBMC. Searches for a matching function call and removes all local variables
/// that are only used in that call as parameters.
class slice_function_callst
{
  const std::regex slice_function;

  std::set<irep_idt> compute_variable_set(const goto_functiont &);

  slice_nodest get_function_parameters(
    const std::set<irep_idt> &,
    const std::set<irep_idt> &,
    unsigned location_number);
  bool is_referenced(const goto_programt::instructiont &, const irep_idt &);

  /// Visitor `exprt` and collect symbol identifiers that are used are used in
  /// it
  class local_variable_visitort : public const_expr_visitort
  {
    std::set<irep_idt> &seen;

  public:
    explicit local_variable_visitort(std::set<irep_idt> &_seen) : seen(_seen)
    {
    }
    void operator()(const exprt &expr) override;
  };

public:
  explicit slice_function_callst(const std::string &_slice_function)
    : slice_function(_slice_function)
  {
  }
  void operator()(goto_functiont &);
};

#endif // CPROVER_GOTO_PROGRAMS_SLICE_FUNCTION_CALLS_H
