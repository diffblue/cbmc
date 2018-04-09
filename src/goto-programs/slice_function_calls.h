/*******************************************************************\

Module: Slice Function Calls and Direct Dependency Parameters

Author: Matthias Güdemann, matthias.guedemann@diffblue.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_SLICE_FUNCTION_CALLS_H
#define CPROVER_GOTO_PROGRAMS_SLICE_FUNCTION_CALLS_H

#include <string>

#include <util/graph.h>

#include "goto_model.h"

void slice_function_calls(goto_model_functiont &, const std::string &);

enum class slice_node_typet
{
  FUNCTION_PARAMETER,
  LOCAL_VARIABLE,
  FUNCTION_CALL,
  OTHER
};

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

class slice_function_callst
{
  const std::string &slice_function;

  std::set<irep_idt> compute_variable_set(const goto_functiont &);

  slice_nodest get_function_parameters(
    const std::set<irep_idt> &,
    const std::set<irep_idt> &,
    unsigned location_number);
  bool is_referenced(
    const goto_programt::instructiont &,
    const std::set<irep_idt> &,
    const irep_idt &);

  /// visit `exprt` and collect symbols that represent local variables that are
  /// referenced in it
  class local_variable_visitort : public const_expr_visitort
  {
    const std::set<irep_idt> &variable_set;
    std::set<irep_idt> &seen;
  public:
    local_variable_visitort(
      const std::set<irep_idt> &_variable_set,
      std::set<irep_idt> &_seen)
      : variable_set(_variable_set), seen(_seen)
    {
    }
    void operator()(const exprt &expr) override;
  };

public:
  slice_function_callst(const std::string &_slice_function)
    : slice_function(_slice_function)
  {
  }
  void operator()(goto_model_functiont &);
};

#endif // CPROVER_GOTO_PROGRAMS_SLICE_FUNCTION_CALLS_H
