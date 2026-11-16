/*******************************************************************\

Module: Objects reachable from a set of pointers

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Objects reachable from a set of pointers, given a pointer analysis. This
/// implements the `havoc_reachable` statement (see `asm_approximationt`) for
/// the analyses that work on goto programs.

#ifndef CPROVER_POINTER_ANALYSIS_REACHABLE_OBJECTS_H
#define CPROVER_POINTER_ANALYSIS_REACHABLE_OBJECTS_H

#include <util/expr.h>
#include <util/std_expr.h>

#include <functional>
#include <vector>

class namespacet;
class symbol_table_baset;

/// The result of \ref find_reachable_objects.
struct reachable_objectst
{
  /// The objects reachable, as root objects of object descriptors (symbols,
  /// dynamic objects, ...), each listed once.
  std::vector<exprt> objects;

  /// The pointers stored in the reachable objects, as lvalues (possibly
  /// containing dereferences) of pointer type.
  std::vector<exprt> pointers;

  /// Whether some pointer has unknown targets.
  bool has_unknown_targets = false;
};

/// Returns the targets (object descriptors, `unknown`, or `invalid`) of the
/// pointer-typed expression it is given, as a value set does.
using get_pointer_targetst = std::function<std::vector<exprt>(const exprt &)>;

/// Computes the objects reachable from the objects \p root_pointers point to
/// and from \p root_objects, following the pointers stored in reachable
/// objects (members of structs and unions, elements of arrays) transitively.
/// Objects are traversed with the type of the pointer through which they are
/// reached, so that objects whose type is unknown to the pointer analysis
/// (such as dynamic objects) are traversed as well.
/// \param root_pointers: Pointer-typed expressions
/// \param root_objects: Objects (lvalues)
/// \param get_targets: The pointer analysis
/// \param ns: Namespace
/// \return The reachable objects and the pointers stored in them
reachable_objectst find_reachable_objects(
  const std::vector<exprt> &root_pointers,
  const std::vector<exprt> &root_objects,
  const get_pointer_targetst &get_targets,
  const namespacet &ns);

/// \return The objects of static lifetime in \p symbol_table, excluding
///   objects of incomplete type and objects used internally by CPROVER,
///   sorted by name. Constant objects are included, as they may contain
///   pointers to objects that can be modified.
std::vector<symbol_exprt> static_lifetime_objects(
  const symbol_table_baset &symbol_table,
  const namespacet &ns);

/// The maximum number of objects \ref reachable_pointer_value lists
/// explicitly.
const std::size_t max_reachable_pointer_candidates = 64;

/// \return An expression whose value set is what the pointer \p pointer,
///   stored in one of the objects of \p reachable, may point to after these
///   objects have been changed: its previous value, the address of any of the
///   reachable objects of a compatible type, or null. With more than
///   \ref max_reachable_pointer_candidates such objects, the pointer may point
///   to any (unknown) object instead. This is a nondeterministic choice, and
///   only meaningful to pointer analyses.
exprt reachable_pointer_value(
  const exprt &pointer,
  const reachable_objectst &reachable);

/// \return True iff a pointer of type \p candidate may be stored in a pointer
///   of type \p location without changing what kind of object it points to:
///   the pointed-to types are the same, or one of them is `void` or a byte.
bool is_compatible_pointer(const typet &location, const typet &candidate);

#endif // CPROVER_POINTER_ANALYSIS_REACHABLE_OBJECTS_H
