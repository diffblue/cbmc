/*******************************************************************\

Module: Local safe pointer analysis

Author: Diffblue Ltd

\*******************************************************************/

/// \file
/// Local safe pointer analysis

#ifndef CPROVER_ANALYSES_LOCAL_SAFE_POINTERS_H
#define CPROVER_ANALYSES_LOCAL_SAFE_POINTERS_H

#include <goto-programs/goto_program.h>
#include <util/std_expr.h>

/// A very simple, cheap analysis to determine when dereference operations are
/// trivially guarded by a check against a null pointer access.
/// In the interests of a very cheap analysis we only search for very local
/// guards -- at the moment only `if(x != null) { *x }`
/// and `assume(x != null); *x` are handled. Control-flow convergence and
/// possibly-aliasing operations are handled pessimistically.
class local_safe_pointerst
{
  /// Comparator that regards base_type_eq expressions as equal, and otherwise
  /// uses the natural (operator<) ordering on irept.
  /// An expression is base_type_eq another one if their types, and types of
  /// their subexpressions, are identical except that one may use a symbol_typet
  /// while the other uses that type's expanded (namespacet::follow'd) form.
  class base_type_comparet
  {
    const namespacet &ns;

  public:
    explicit base_type_comparet(const namespacet &ns)
      : ns(ns)
    {
    }

    base_type_comparet(const base_type_comparet &other)
      : ns(other.ns)
    {
    }

    base_type_comparet &operator=(const base_type_comparet &other)
    {
      INVARIANT(&ns == &other.ns, "base_type_comparet: clashing namespaces");
      return *this;
    }

    bool operator()(const exprt &e1, const exprt &e2) const;
  };

  std::map<unsigned, std::set<exprt, base_type_comparet>> non_null_expressions;

  const namespacet &ns;

public:
  local_safe_pointerst(const namespacet &ns)
    : ns(ns)
  {
  }

  void operator()(const goto_programt &goto_program);

  bool is_non_null_at_program_point(
    const exprt &expr, goto_programt::const_targett program_point);

  bool is_safe_dereference(
    const dereference_exprt &deref,
    goto_programt::const_targett program_point)
  {
    return is_non_null_at_program_point(deref.op(), program_point);
  }

  void output(std::ostream &stream, const goto_programt &program);

  void output_safe_dereferences(
    std::ostream &stream, const goto_programt &program);
};

#endif // CPROVER_ANALYSES_LOCAL_SAFE_POINTERS_H
