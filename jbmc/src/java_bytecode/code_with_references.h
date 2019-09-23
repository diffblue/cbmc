/*******************************************************************\

Module: Java bytecode

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_CODE_WITH_REFERENCES_H
#define CPROVER_JAVA_BYTECODE_CODE_WITH_REFERENCES_H

#include <memory>
#include <util/std_code.h>

/// Allocate a fresh array of length \p array_length_expr and assigns \p expr
/// to it.
codet allocate_array(
  const exprt &expr,
  const exprt &array_length_expr,
  const source_locationt &loc);

/// Information to store when several references point to the same Java object.
struct object_creation_referencet
{
  /// Expression for the symbol that stores the value that may be reference
  /// equal to other values.
  exprt expr;

  /// If `symbol` is an array, this expression stores its length.
  /// This should only be set once the actual elements of the array have been
  /// seen, not the first time an `@ref` have been seen, only when `@id` is
  /// seen.
  optionalt<exprt> array_length;
};

/// Base class for code which can contain references which can get replaced
/// before generating actual codet.
/// Currently only references in array allocations are supported, because this
/// is currently the only use required by \ref assign_from_json.
class code_with_referencest
{
public:
  using reference_substitutiont =
    std::function<const object_creation_referencet &(const std::string &)>;

  virtual code_blockt to_code(reference_substitutiont &) const = 0;

  virtual ~code_with_referencest() = default;
};

/// Code that should not contain reference
class code_without_referencest : public code_with_referencest
{
public:
  codet code;

  explicit code_without_referencest(codet code) : code(std::move(code))
  {
  }

  code_blockt to_code(reference_substitutiont &) const override
  {
    return code_blockt({code});
  }
};

/// Allocation code which contains a reference.
/// The generated code will be of the form:
///
///         array_length = nondet(int)
///         assume(array_length >= 0)
///         array_expr = new array_type[array_length];
///
/// Where array_length and array_expr are given by the reference substitution
/// function.
class reference_allocationt : public code_with_referencest
{
public:
  std::string reference_id;
  source_locationt loc;

  reference_allocationt(std::string reference_id, source_locationt loc)
    : reference_id(std::move(reference_id)), loc(std::move(loc))
  {
  }

  code_blockt to_code(reference_substitutiont &references) const override;
};

/// Wrapper around a list of shared pointer to code_with_referencest objects,
/// which provides a nicer interface.
class code_with_references_listt
{
public:
  std::list<std::shared_ptr<code_with_referencest>> list;

  void add(code_without_referencest code);

  void add(codet code);

  void add(reference_allocationt ref);

  void append(code_with_references_listt &&other);

  void add_to_front(code_without_referencest code);
};

#endif // CPROVER_JAVA_BYTECODE_CODE_WITH_REFERENCES_H
