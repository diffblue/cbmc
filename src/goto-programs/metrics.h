/*******************************************************************\

Module: Provides metrics for the complexity call graph

Author: Benjamin Quiring

\*******************************************************************/

/// \file
/// Provides metrics used for the complexity call graph

#ifndef CPROVER_COMPLEXITY_GRAPH_METRICS_H
#define CPROVER_COMPLEXITY_GRAPH_METRICS_H

#include <goto-programs/goto_program.h>
#include <map>

class namespacet;
class goto_functionst;

class solver_infot
{
  public:
  // the number of clauses, literals, and variables
  int clauses = 0;
  int literals = 0;
  int variables = 0;

  // Adds together this and another solver_info
  // \param other: the other solver_info to add
  // \return: this solver_info
  solver_infot &operator+= (const solver_infot &other)
  {
    clauses += other.clauses;
    literals += other.literals;
    variables += other.variables;
    return *this;
  }

  // Adds together this and another solver_info
  // \param other: the other solver_info to add
  // \return: the sum of this solver_info and the other
  solver_infot operator+(const solver_infot &other)
  {
    solver_infot info (*this);
    info += other;
    return info;
  }
};

class symex_infot
{
  public:
  // number of symex steps
  int steps = 0;
  // duration of symex steps (in nanoseconds)
  double duration = 0.0;

  // Adds together this and another symex_info
  // \param other: the other solver_info to add
  // \return: this solver_info
  symex_infot &operator+= (const symex_infot &other)
  {
    steps += other.steps;
    duration += other.duration;
    return *this;
  }

  // Adds together this and another symex_info
  // \param other: the other solver_info to add
  // \return: the sum of this solver_info and the other
  symex_infot operator+(const symex_infot &other)
  {
    symex_infot info(*this);
    info += other;
    return info;
  }

};


class func_metricst
{

 public:
  // how many calls to function pointers are in the function's body
  int num_func_pointer_calls = 0;

  // sum of the sides of all right-hand sides in the function body
  int function_size = 0;

  // number of high-complexity primitives in the function's body
  // e.g. struct field access, array indexing, pointer dereferencing
  int num_complex_user_ops = 0;

  // number of standard library functions called
  // e.g. memcpy, memmove, memcmp, malloc, free, realloc
  int num_complex_lib_funcs = 0;

  // number of high-complexity CBMC-internal functions
  // e.g. byte_extract_little_endian,
  //      byte_extract_big_endian,
  //      byte_update_little_endian,
  //      byte_update_big_endian,
  int num_complex_cbmc_ops = 0;

  // number of loops (backwards jumps) in the function's body
  int num_loops = 0;

  // wheter there is valid symex info
  bool use_symex_info = false;
  symex_infot symex_info;

  // wheter there is valid solver info
  bool use_solver_info = false;
  solver_infot solver_info;

  // Dumps an html representation of this metrics
  // \param out: the output stream to dump to
  const void dump_html (std::ostream &out) const;

  // average symex time per step in nanoseconds/step
  const double avg_time_per_symex_step () const;

};

using instruction_collectiont = std::vector<std::vector<goto_programt::const_targett>>;

int num_loops (const instruction_collectiont &instructions);

int function_size (const instruction_collectiont &instructions);

int num_func_pointer_calls (const instruction_collectiont &instructions);

int num_complex_user_ops (const instruction_collectiont &instructions);

int num_complex_lib_funcs (const instruction_collectiont &instructions, const std::set<irep_idt> &lib_funcs);

int num_complex_cbmc_ops (const instruction_collectiont &instructions);

symex_infot aggregate_symex_info (const instruction_collectiont &instructions,
                                  const std::map<goto_programt::const_targett, symex_infot> &instr_symex_info);

solver_infot aggregate_solver_info (const instruction_collectiont &instructions,
                                    const std::map<goto_programt::const_targett, solver_infot> &instr_symex_info);

template<class T> T aggregate_instr_info (
  const instruction_collectiont &instructions,
  const std::map<goto_programt::const_targett, T> &instr_info)
{
  T total;
  for (const auto &insts : instructions)
  {
    for (const auto &target : insts)
    {
      const auto &info = instr_info.find (target);
      if (info != instr_info.end())
      {
        const T &other = info->second;
        total += other;
      }
    }
  }
  return total;
}

#endif // CPROVER_GOTO_PROGRAMS_PROOF_CFG_METRICS_H
