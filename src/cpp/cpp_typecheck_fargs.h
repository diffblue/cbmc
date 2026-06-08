/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifndef CPROVER_CPP_CPP_TYPECHECK_FARGS_H
#define CPROVER_CPP_CPP_TYPECHECK_FARGS_H

#include <util/expr.h>

#include "cpp_target_type.h"

class code_typet;
class cpp_typecheckt;
class side_effect_expr_function_callt;
class cpp_scopet;

class cpp_typecheck_fargst // for function overloading
{
public:
  bool in_use, has_object;
  exprt::operandst operands;

  /// The scope of the point of use for access control ([class.access]):
  /// the enclosing class/function in which the name being resolved
  /// textually appears.  For an explicit-object member access
  /// (`obj.member`) the resolver navigates into the object's class scope
  /// before looking the member up, which would otherwise lose the
  /// genuine point of use.  When set, this is the scope from which
  /// member accessibility is judged; when null, the resolver falls back
  /// to the scope active at resolution time.
  cpp_scopet *naming_scope = nullptr;

  /// Optional target type for the enclosing context, propagated to
  /// the resolver so that template-argument deduction has access to
  /// the call site's context-driven type ([temp.deduct.funcaddr]/1,
  /// [temp.deduct.conv]/1).  An empty (default) instance carries no
  /// constraint; this matches the pre-target-type-threading
  /// behaviour.  See `cpp_target_type.h` and
  /// `doc/architectural/cpp-frontend-plan-target-type-threading.md`.
  ///
  /// Phase 1C of the refactor: the field is in place but the
  /// resolver does not yet read it; subsequent phases add the
  /// consumption sites.
  target_typet target;

  // has_object indicates that the first element of
  // 'operands' is the 'this' pointer (with the object type,
  // not pointer to object type)

  cpp_typecheck_fargst() : in_use(false), has_object(false)
  {
  }

  bool has_class_type() const;

  void build(
    const side_effect_expr_function_callt &function_call);

  explicit cpp_typecheck_fargst(
    const side_effect_expr_function_callt &function_call):
    in_use(false), has_object(false)
  {
    build(function_call);
  }

  bool match(
    const code_typet &code_type,
    unsigned &distance,
    cpp_typecheckt &cpp_typecheck) const;

  void add_object(const exprt &expr)
  {
    // if(!in_use) return;
    has_object=true;
    operands.insert(operands.begin(), expr);
  }

  void remove_object()
  {
    PRECONDITION(has_object);
    operands.erase(operands.begin());
    has_object = false;
  }
};

#endif // CPROVER_CPP_CPP_TYPECHECK_FARGS_H
