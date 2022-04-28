// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_OBJECT_TRACKING_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_OBJECT_TRACKING_H

#include <util/expr.h>
#include <util/pointer_expr.h>

#include <unordered_map>

/// Information the decision procedure holds about each object.
struct decision_procedure_objectt
{
  /// The expression for the root of the object. This is expression equivalent
  /// to deferencing a pointer to this object with a zero offset.
  exprt base_expression;
  /// Number which uniquely identifies this particular object.
  std::size_t unique_id;
  /// Expression which evaluates to the size of the object in bytes.
  exprt size;
};

/// The model of addresses we use consists of a unique object identifier and an
/// offset. In order to encode the offset identifiers we need to assign unique
/// identifiers to the objects. This function finds the base object expression
/// in an address of expression for which a unique identifier needs to be
/// assigned.
exprt find_object_base_expression(const address_of_exprt &address_of);

/// Arbitary expressions passed to the decision procedure may have multiple
/// address of operations as its sub expressions. This means the overall
/// expression may contain multiple base objects which need to be assigned
/// unique identifiers.
/// \param expression
///   The expression within which to find base objects.
/// \param output_object
///   This function is called with each of the base object expressions found, as
///   they are found.
/// \details
///   The found objects are returned through an output function in order to
///   separate the implementation of the storage and deduplication of the
///   results from finding the object expressions. The type of \p output_object
///   is a template parameter in order to eliminate potential performance
///   overheads of using `std::function`.
template <typename output_object_functiont>
void find_object_base_expressions(
  const exprt &expression,
  const output_object_functiont &output_object)
{
  expression.visit_pre([&](const exprt &node) {
    if(const auto address_of = expr_try_dynamic_cast<address_of_exprt>(node))
    {
      output_object(find_object_base_expression(*address_of));
    }
  });
}

/// Mapping from an object's base expression to the set of information about it
/// which we track.
using smt_object_mapt =
  std::unordered_map<exprt, decision_procedure_objectt, irep_hash>;

/// Constructs an initial object map containing the null object. The null object
/// must be added at construction in order to ensure it is allocated a unique
/// identifier of 0.
smt_object_mapt initial_smt_object_map();

/// \brief
///   Finds all the object expressions in the given expression and adds them to
///   the object map for cases where the map does not contain them already.
/// \param expression
///   The expression within which to find and base object expressions.
/// \param ns
///   The namespace used to look up the size of object types.
/// \param object_map
///   The map into which any new tracking information should be inserted.
void track_expression_objects(
  const exprt &expression,
  const namespacet &ns,
  smt_object_mapt &object_map);

/// Finds whether all base object expressions in the given expression are
/// already tracked in the given object map. This supports writing invariants
/// on the base object expressions already being tracked in the map in contexts
/// where the map is const.
bool objects_are_already_tracked(
  const exprt &expression,
  const smt_object_mapt &object_map);

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_OBJECT_TRACKING_H
