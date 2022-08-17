/*******************************************************************\

Module: Compute metrics for the Proof CFG

Author: Benjamin Quiring

\*******************************************************************/

/// \file
/// Compute metrics used for the CFG rendering

#ifndef CPROVER_COMPLEXITY_GRAPH_METRICS_H
#define CPROVER_COMPLEXITY_GRAPH_METRICS_H

#include <goto-programs/goto_program.h>
#include <map>

class namespacet;
class goto_functionst;

class solver_infot {
  public:
  int clauses = 0;
  int literals = 0;
  int variables = 0;

  solver_infot &operator+= (const solver_infot &other) {
    clauses += other.clauses;
    literals += other.literals;
    variables += other.variables;
    return *this;
  }

  solver_infot operator+(const solver_infot &other) {
    solver_infot info (*this);
    info += other;
    return info;
  }
};

class symex_infot {
  public:
  // number of symex steps
  int steps = 0;
  // duration of symex steps (in nanoseconds) 
  double duration = 0.0;

  symex_infot &operator+= (const symex_infot &other) {
    steps += other.steps;
    duration += other.duration;
    return *this;
  }

  symex_infot operator+(const symex_infot &other) {
    symex_infot info(*this);
    info += other;
    return info;
  }

};


class func_metricst {
  
 public:
  // how many calls to function pointers are in the function's body
  int num_func_pointer_calls = 0;
  // sum of the sides of all right-hand sides in the function body
  int function_size = 0;
  // number of high-complexity primitives in the function's body
  // e.g. memcpy, memmove, memcmp, malloc, free, realloc
  //      struct field access, array indexing, pointer dereferencing
  int num_complex_user_ops = 0;
  int num_complex_lib_funcs = 0;
  // number of high-complexity CBMC-internal functions
  // e.g. byte_extract_little_endian,
  //      byte_extract_big_endian,
  //      byte_update_little_endian,
  //      byte_update_big_endian,
  int num_complex_cbmc_ops = 0;
  // number of loops (backwards jumps) in the function's body
  int num_loops = 0;
  // number of join points
  int num_join_points = 0;

  bool use_symex_info = false;
  symex_infot symex_info;
  bool use_solver_info = false;
  solver_infot solver_info;

  const void dump_html (std::ostream &out) const;

  // avg time in nanoseconds
  const double avg_time_per_symex_step () const;

};

int num_loops (const std::vector<std::vector<goto_programt::const_targett>> &instructions);

int function_size (const std::vector<std::vector<goto_programt::const_targett>> &instructions);

int num_func_pointer_calls (const std::vector<std::vector<goto_programt::const_targett>> &instructions);

int num_complex_user_ops (const std::vector<std::vector<goto_programt::const_targett>> &instructions);

int num_complex_lib_funcs (const std::vector<std::vector<goto_programt::const_targett>> &instructions, const std::set<std::string> &lib_funcs);

int num_complex_cbmc_ops (const std::vector<std::vector<goto_programt::const_targett>> &instructions);

symex_infot aggregate_symex_info (const std::vector<std::vector<goto_programt::const_targett>> &instructions,
                                  const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info);

solver_infot aggregate_solver_info (const std::vector<std::vector<goto_programt::const_targett>> &instructions,
                                    const std::map<goto_programt::const_targett, solver_infot> &instr_symex_info);

template<class T> T aggregate_instr_info
  (const std::vector<std::vector<goto_programt::const_targett>> &instructions,
   const std::map<goto_programt::const_targett, T> &instr_info) {
  T total;
  for (const auto &insts : instructions) {
    for (const auto &target : insts) {
      const auto &info = instr_info.find (target);
      if (info != instr_info.end()) {
        const T &other = info->second;
        total += other;
      }
    }
  }
  return total;
}

#endif // CPROVER_GOTO_PROGRAMS_PROOF_CFG_METRICS_H
