/*******************************************************************\

Module: Java Bytecode Language Conversion

Author: Diffblue Ltd.

\*******************************************************************/
#ifndef CPROVER_JAVA_BYTECODE_SELECT_POINTER_TYPE_H
#define CPROVER_JAVA_BYTECODE_SELECT_POINTER_TYPE_H

/// \file
/// Handle selection of correct pointer type (for example changing abstract
/// classes to concrete versions).
#include "generic_parameter_specialization_map.h"
#include "java_types.h"

#include <vector>

#include "java_types.h"
#include <util/optional.h>
#include <util/std_types.h>

class namespacet;

class select_pointer_typet
{
public:
  virtual ~select_pointer_typet() = default;

  /// Select what type should be used for a given pointer type. In the base
  /// class we just use the supplied type. Derived classes can override this
  /// behavior to provide more sophisticated type selection. Generic
  /// parameters are replaced with their specialized type.
  /// \param pointer_type: The pointer type to convert
  /// \param generic_parameter_specialization_map: Map of types for all generic
  ///   parameters in the current scope
  /// \param ns: Namespace for type lookups
  /// \return A pointer type where the subtype may have been modified
  virtual pointer_typet convert_pointer_type(
    const pointer_typet &pointer_type,
    const generic_parameter_specialization_mapt
      &generic_parameter_specialization_map,
    const namespacet &ns) const;

  /// Get alternative types for a method parameter, e.g., based on the casts in
  /// the function body. In the base class we just return an empty set.
  /// Derived classes can override this behaviour to provide more
  /// sophisticated alternative type identification.
  virtual std::set<struct_tag_typet> get_parameter_alternative_types(
    const irep_idt &function_name,
    const irep_idt &parameter_name,
    const namespacet &ns) const;

  /// Specialize generic parameters in a pointer type based on the current map
  /// of parameters -> types. We specialize generics only if the pointer is a
  /// java generic parameter or an array with generic parameters. More
  /// general generic types such as `MyGeneric<T>` are specialized
  /// indirectly in \ref java_object_factoryt, their concrete types are already
  /// stored in the map and will be retrieved when needed e.g., to initialize
  /// fields.
  /// Example:
  /// - generic type: T
  /// - map: T -> U; U -> String
  /// - result: String
  ///
  /// - generic type: T[]
  /// - map: T -> U; U -> String
  /// - result: String[]
  /// Example 2:
  /// `class MyGeneric<T,U> { MyGeneric<U,T> gen; T t;}`
  /// When instantiating `MyGeneric<Integer,String> my` we need to resolve the
  /// type of `my.gen.t`. The map would in this context contain
  /// - T -> (Integer, U)
  /// - U -> (String, T)
  ///
  /// Note that the top of the stacks for T and U create a recursion T -> U,
  /// U-> T. We break it and specialize `T my.gen.t` to `String my.gen.t`.
  /// \param pointer_type: The pointer to be specialized
  /// \param generic_parameter_specialization_map: Map of types for all
  ///   generic parameters in the current scope
  /// \return Pointer type where generic parameters are replaced with
  ///   specialized types (if set in the current scope)
  pointer_typet specialize_generics(
    const pointer_typet &pointer_type,
    const generic_parameter_specialization_mapt
      &generic_parameter_specialization_map) const;
};

#endif // CPROVER_JAVA_BYTECODE_SELECT_POINTER_TYPE_H
