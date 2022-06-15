/*******************************************************************\

Module: Compute metrics for the Proof CFG

Author: Benjamin Quiring

\*******************************************************************/

/// \file
/// Compute metrics used for the CFG rendering

#ifndef CPROVER_GOTO_PROGRAMS_PROOF_CFG_METRICS_H
#define CPROVER_GOTO_PROGRAMS_PROOF_CFG_METRICS_H

#include "goto_program.h"
#include <util/ui_message.h>
#include <map>

class solver_infot {
  public:
  int clauses;
  int literals;
  int variables;
};

class symex_infot {
  public:
  int steps;
  double duration;
};


class namespacet;
class goto_functionst;

class func_metrics {
  
 public:
  // how many times is the function called
  int indegree;
  // how many function calls are in the function's body
  int outdegree;
  // how many calls to function pointers are in the function's body
  int num_func_pointer_calls;
  // sum of the sides of all right-hand sides in the function body
  int function_size;
  // number of high-complexity primitives in the function's body
  // e.g. TODO: memcpy, memmove, memcmp
  //      writes to pointers, arrays
  int num_complex_ops;
  // number of loops (backwards jumps) in the function's body
  int num_loops;
  // number of steps inside this function in symex
  int symex_steps;
  // duration of symex steps (in nanoseconds) for this function
  double symex_duration;

  int solver_clauses;
  int solver_literals;
  int solver_variables;

  func_metrics () {
    indegree = 0;
    outdegree = 0;
    num_func_pointer_calls = 0;
    function_size = 0;
    num_complex_ops = 0;
    num_loops = 0;

    symex_steps = 0;
    symex_duration = 0.0;

    solver_clauses=0;
    solver_literals=0;
    solver_variables=0;
  }

  const void dump_html (messaget &msg) const;

  // avg time in nanoseconds
  const double avg_time_per_symex_step () const;

};

int num_loops (const goto_programt &goto_program);

int outdegree (const goto_programt &goto_program);

int indegree (const symbolt &symbol, 
              const namespacet &ns, 
              const goto_functionst &goto_functions);

int function_size (const goto_programt &goto_program);

int num_complex_ops (const goto_programt &goto_program);

symex_infot aggregate_symex_info (const goto_programt &goto_program,
                                  const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info);

solver_infot aggregate_solver_info (const goto_programt &goto_program,
                                    const std::map<goto_programt::const_targett, solver_infot> &instr_symex_info);

#endif // CPROVER_GOTO_PROGRAMS_PROOF_CFG_METRICS_H
