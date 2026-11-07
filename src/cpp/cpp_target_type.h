/*******************************************************************\

Module: C++ Language Type Checking — target type for overload resolution

Author: Michael Tautschnig (with Kiro)

\*******************************************************************/

/// \file
/// Target-type context for C++ overload resolution and template-argument
/// deduction.
///
/// Several C++ deduction and conversion paths require the typechecker
/// to know the *target type* of an expression while typechecking it:
///
/// * [temp.deduct.funcaddr]/1 — taking the address of a function
///   template; the template arguments are deduced from the target
///   pointer-to-function type.
/// * [temp.deduct.conv]/1 — instantiating a conversion-function
///   template; arguments are deduced by comparing the return type
///   against the required conversion target.
/// * [over.ics.list] / [dcl.init.list] — brace-init-list arguments
///   are matched against the target type (e.g.,
///   `initializer_list<T>` or aggregate fields).
///
/// Without this context CBMC pre-typechecks every operand in
/// isolation, then patches up the result against the expected type.
/// This works for simple cases but cannot drive deduction.
/// `target_typet` carries the optional target through the typecheck
/// API so the resolver can use it where the standard prescribes.
///
/// The class is non-owning: the caller must keep the referenced
/// type alive for the duration of the typecheck call.  In practice
/// the target is always a member of an existing
/// `code_typet::parameter_type()`, a `symbolt::type`, or similar
/// long-lived storage.

#ifndef CPROVER_CPP_CPP_TARGET_TYPE_H
#define CPROVER_CPP_CPP_TARGET_TYPE_H

class typet;

/// Optional target-type context propagated through C++ expression
/// typechecking.  An empty (default-constructed) instance carries no
/// constraint.  See `cpp_target_type.h` for the standard background.
class target_typet
{
public:
  /// No target type — the default; matches the pre-target-type-threading
  /// behaviour where each operand is typechecked in isolation.
  target_typet() = default;

  /// Target type known.  The referenced \p t must outlive this object.
  explicit target_typet(const typet &t) : target(&t)
  {
  }

  /// Pointer to the target type, or `nullptr` if none.
  const typet *get() const
  {
    return target;
  }

  /// True when a target type is set.
  bool has_target() const
  {
    return target != nullptr;
  }

private:
  const typet *target = nullptr;
};

#endif // CPROVER_CPP_CPP_TARGET_TYPE_H
