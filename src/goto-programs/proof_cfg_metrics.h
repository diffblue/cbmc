/*******************************************************************\

Module: Compute metrics for the Proof CFG

Author: Benjamin Quiring

\*******************************************************************/

/// \file
/// Compute metrics used for the CFG rendering

#ifndef CPROVER_GOTO_PROGRAMS_PROOF_CFG_METRICS_H
#define CPROVER_GOTO_PROGRAMS_PROOF_CFG_METRICS_H

#include "goto_program.h"

class namespacet;
class goto_functionst;

struct func_metrics {
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
};

int num_loops (const goto_programt &goto_program);

int outdegree (const goto_programt &goto_program);

int indegree (const symbolt &symbol, 
              const namespacet &ns, 
              const goto_functionst &goto_functions);

int function_size (const goto_programt &goto_program);

int num_complex_ops (const goto_programt &goto_program);

#endif // CPROVER_GOTO_PROGRAMS_PROOF_CFG_METRICS_H
