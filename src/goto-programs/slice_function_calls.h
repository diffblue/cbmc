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
  FUNCTION_CALL
};

struct slice_param_boundst
{
  unsigned upper_bound = 0;
  unsigned lower_bound = 0;
};

struct slice_nodet : public graph_nodet<empty_edget>
{
  slice_node_typet slice_node_type;
  irep_idt name;
  // bounds only used for local variables
  slice_param_boundst slice_param_bounds;
  unsigned location_number = 0;
  node_indext node_index;
};

typedef grapht<slice_nodet> slice_function_grapht;
typedef std::list<slice_nodet> slice_nodest;

class slice_function_callst
{
  const std::string &slice_function;

  // maps a variable name to a list of scopes in the form of instruction numbers
  // bounds
  typedef std::map<irep_idt, std::list<slice_param_boundst>>
    variable_bounds_mapt;
  variable_bounds_mapt compute_variable_bounds(const goto_functiont &);

  slice_nodest get_function_parameters(
    variable_bounds_mapt &,
    const std::set<irep_idt> &,
    unsigned location_number);
  bool is_referenced(
    const goto_programt::instructiont &,
    const variable_bounds_mapt &,
    const irep_idt &);

  /// visit `exprt` and collect symbols that represent local variables that are
  /// referenced in it
  class local_variable_visitort : public const_expr_visitort
  {
    const variable_bounds_mapt &variable_bounds_map;
    std::set<irep_idt> &seen;
  public:
    local_variable_visitort(
      const variable_bounds_mapt &_variable_bounds_map,
      std::set<irep_idt> &_seen)
      : variable_bounds_map(_variable_bounds_map), seen(_seen)
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
