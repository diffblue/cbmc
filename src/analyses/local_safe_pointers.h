/*******************************************************************\

Module: Local safe pointer analysis

Author: Diffblue Ltd

\*******************************************************************/

/// \file
/// Local safe pointer analysis

#ifndef CPROVER_ANALYSES_LOCAL_SAFE_POINTERS_H
#define CPROVER_ANALYSES_LOCAL_SAFE_POINTERS_H

#include <util/pointer_expr.h>

#include <goto-programs/goto_program.h>

#include <map>
#include <unordered_set>

/// A very simple, cheap analysis to determine when dereference operations are
/// trivially guarded by a check against a null pointer access.
/// In the interests of a very cheap analysis we only search for very local
/// guards -- at the moment only `if(x != null) { *x }`
/// and `assume(x != null); *x` are handled. Control-flow convergence and
/// possibly-aliasing operations are handled pessimistically.
class local_safe_pointerst
{
  /// Comparator that regards type-equal expressions as equal, and otherwise
  /// uses the natural (operator<) ordering on irept.
  struct type_comparet
  {
    bool operator()(const exprt &e1, const exprt &e2) const
    {
      return e1.type() != e2.type() && e1 < e2;
    }
  };

  std::map<unsigned, std::set<exprt, type_comparet>> non_null_expressions;

  /// Dereferences that are guarded by a conditional null-check appearing in the
  /// same instruction, e.g. `(p != null) ? *p : x` (such conditional
  /// expressions are produced by if-conversion in place of `if(p != null) *p`).
  /// Mapped from instruction location number to the set of safe
  /// `dereference_exprt`s, matched exactly.
  std::map<unsigned, std::unordered_set<exprt, irep_hash>>
    if_guarded_dereferences;

public:
  void operator()(const goto_programt &goto_program);

  bool is_non_null_at_program_point(
    const exprt &expr, goto_programt::const_targett program_point);

  bool is_safe_dereference(
    const dereference_exprt &deref,
    goto_programt::const_targett program_point)
  {
    if(is_non_null_at_program_point(deref.op(), program_point))
      return true;

    // The pointer may instead be guarded by a conditional null-check within
    // this very instruction, e.g. `(p != null) ? *p : x`.
    auto findit = if_guarded_dereferences.find(program_point->location_number);
    return findit != if_guarded_dereferences.end() &&
           findit->second.find(deref) != findit->second.end();
  }

  void output(
    std::ostream &stream,
    const goto_programt &program,
    const namespacet &ns);

  void output_safe_dereferences(
    std::ostream &stream,
    const goto_programt &program,
    const namespacet &ns);
};

#endif // CPROVER_ANALYSES_LOCAL_SAFE_POINTERS_H
