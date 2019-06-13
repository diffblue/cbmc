/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier <romain.brenguier@diffblue.com>

*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_SSA_STEP_H
#define CPROVER_GOTO_SYMEX_SSA_STEP_H

#include <goto-programs/goto_trace.h>

#include "symex_target.h"

/// Single SSA step in the equation. Its `type` is defined as
/// goto_trace_stept::typet. Every SSA step has a `source` to identify its
/// origin in the input GOTO program and a `guard` expression which holds
/// the path condition required to reach this step: they limit the scope of
/// this step.
///
/// SSA steps that represent assignments and declarations also store the
/// left- and right-hand sides of the assignment. The left-hand side
/// `ssa_lhs` is required to be of type ssa_exprt: in SSA form, variables
/// are only assigned once, see \ref static-single-assignment. To achieve
/// that, we annotate the original name with 3 types of levels, see
/// ssa_exprt. The assignment step also represents the left-hand side in two
/// other _full_ forms: `ssa_full_lhs` and `original_full_lhs`, which store
/// the original expressions from the input GOTO program before removing
/// array indexes, pointers, etc. The `ssa_full_lhs` uses the level-annotated
/// names.
///
/// Assumptions, assertions, goto steps, and constraints have `cond_expr`
/// which represent the condition guarding this step, i.e. what must hold for
/// this step to be taken. Both `guard` and `cond_expr` will later be
/// translated into verification condition for the SAT/SMT solver (or some
/// other decision procedure), to be referred by their respective handles.
/// Constraints usually arise from external conditions, such as memory models
/// or partial orders: they represent assumptions with global effect.
///
/// Function calls store `called_function` name as well as a vector of
/// arguments `ssa_function_arguments`. The `converted` version of a
/// variable will contain its version for the SAT/SMT conversion.
class SSA_stept
{
public:
  symex_targett::sourcet source;
  goto_trace_stept::typet type;

  bool is_assert() const
  {
    return type == goto_trace_stept::typet::ASSERT;
  }

  bool is_assume() const
  {
    return type == goto_trace_stept::typet::ASSUME;
  }

  bool is_assignment() const
  {
    return type == goto_trace_stept::typet::ASSIGNMENT;
  }

  bool is_goto() const
  {
    return type == goto_trace_stept::typet::GOTO;
  }

  bool is_constraint() const
  {
    return type == goto_trace_stept::typet::CONSTRAINT;
  }

  bool is_location() const
  {
    return type == goto_trace_stept::typet::LOCATION;
  }

  bool is_output() const
  {
    return type == goto_trace_stept::typet::OUTPUT;
  }

  bool is_decl() const
  {
    return type == goto_trace_stept::typet::DECL;
  }

  bool is_function_call() const
  {
    return type == goto_trace_stept::typet::FUNCTION_CALL;
  }

  bool is_function_return() const
  {
    return type == goto_trace_stept::typet::FUNCTION_RETURN;
  }

  bool is_shared_read() const
  {
    return type == goto_trace_stept::typet::SHARED_READ;
  }

  bool is_shared_write() const
  {
    return type == goto_trace_stept::typet::SHARED_WRITE;
  }

  bool is_spawn() const
  {
    return type == goto_trace_stept::typet::SPAWN;
  }

  bool is_memory_barrier() const
  {
    return type == goto_trace_stept::typet::MEMORY_BARRIER;
  }

  bool is_atomic_begin() const
  {
    return type == goto_trace_stept::typet::ATOMIC_BEGIN;
  }

  bool is_atomic_end() const
  {
    return type == goto_trace_stept::typet::ATOMIC_END;
  }

  /// Returns the property ID if this is a step resulting from an ASSERT, or
  /// builds a unique name for an unwinding assertion.
  irep_idt get_property_id() const;

  // we may choose to hide
  bool hidden = false;

  exprt guard;
  exprt guard_handle;

  // for ASSIGNMENT and DECL
  ssa_exprt ssa_lhs;
  exprt ssa_full_lhs, original_full_lhs;
  exprt ssa_rhs;
  symex_targett::assignment_typet assignment_type;

  // for ASSUME/ASSERT/GOTO/CONSTRAINT
  exprt cond_expr;
  exprt cond_handle;
  std::string comment;

  // for INPUT/OUTPUT
  irep_idt format_string, io_id;
  bool formatted = false;
  std::list<exprt> io_args;
  std::list<exprt> converted_io_args;

  // for function calls: the function that is called
  irep_idt called_function;

  // for function calls
  std::vector<exprt> ssa_function_arguments, converted_function_arguments;

  // for SHARED_READ/SHARED_WRITE and ATOMIC_BEGIN/ATOMIC_END
  unsigned atomic_section_id = 0;

  // for slicing
  bool ignore = false;

  // for incremental conversion
  bool converted = false;

  SSA_stept(
    const symex_targett::sourcet &_source,
    goto_trace_stept::typet _type)
    : source(_source),
      type(_type),
      hidden(false),
      guard(static_cast<const exprt &>(get_nil_irep())),
      guard_handle(false_exprt()),
      ssa_lhs(static_cast<const ssa_exprt &>(get_nil_irep())),
      ssa_full_lhs(static_cast<const exprt &>(get_nil_irep())),
      original_full_lhs(static_cast<const exprt &>(get_nil_irep())),
      ssa_rhs(static_cast<const exprt &>(get_nil_irep())),
      assignment_type(symex_targett::assignment_typet::STATE),
      cond_expr(static_cast<const exprt &>(get_nil_irep())),
      cond_handle(false_exprt()),
      formatted(false),
      atomic_section_id(0),
      ignore(false)
  {
  }

  void output(std::ostream &out) const;

  void validate(const namespacet &ns, const validation_modet vm) const;
};

class SSA_assignment_stept : public SSA_stept
{
public:
  SSA_assignment_stept(
    symex_targett::sourcet source,
    exprt guard,
    ssa_exprt ssa_lhs,
    exprt ssa_full_lhs,
    exprt original_full_lhs,
    exprt ssa_rhs,
    symex_targett::assignment_typet assignment_type);
};

#endif // CPROVER_GOTO_SYMEX_SSA_STEP_H
