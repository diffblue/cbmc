// Author: Diffblue Ltd.

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_TRANSFORM_HISTORY_H
#define CPROVER_GOTO_PROGRAMS_GOTO_TRANSFORM_HISTORY_H

#include <vector>

class goto_functiont;
class goto_functionst;

enum class goto_transform_kindt;

/// An ordered collection of transformations which have been applied. This
/// collection is encapsulated in a class in order to support -
///  * Writing newly applied transforms to the correct end of the history.
///  * Querying the existing history.
///  * Restricting mutating existing history.
class goto_transform_historyt
{
public:
  using transformst = std::vector<goto_transform_kindt>;

  void add(goto_transform_kindt transform);
  const transformst &transforms() const;

private:
  std::vector<goto_transform_kindt> _transforms;
};

/// Each of the kinds of transformation below are associated with the
/// implementation of a transformation. These associations are as follows -
///  * link_to_library \ref goto-programs/link_to_library.h
///  * string_instrumentation \ref goto-programs/string_instrumentation.h
///  * remove_function_pointers \ref goto-programs/remove_function_pointers.h
///  * mm_io \ref goto-programs/mm_io.h
///  * instrument_preconditions \ref goto-programs/instrument_preconditions.h
///  * goto_partial_inline \ref goto-programs/goto_inline_class.h
///  * remove_returns \ref goto-programs/remove_returns.h
///  * remove_vector \ref goto-programs/remove_vector.h
///  * remove_complex \ref goto-programs/remove_complex.h
///  * rewrite_union \ref goto-programs/rewrite_union.h
///  * transform_assertions_assumptions \ref goto-programs/goto_check.h
///  * adjust_float_expressions \ref goto-programs/adjust_float_expressions.h
///  * string_abstraction \ref goto-programs/string_abstraction.h
///  * remove_unused_functions \ref goto-programs/remove_unused_functions.h
///  * remove_skip \ref goto-programs/remove_skip.h
///  * label_properties \ref goto-programs/set_properties.h
enum class goto_transform_kindt
{
  // Warning! The numeric values in this enumeration are used for serialisation
  // and deserialization. The entries should not be renumbered or removed and
  // reused. The ordering here is not intended to be used for any relational
  // operation. So new identifiers can be allocated sequentially.
  link_to_library = 1,
  string_instrumentation = 2,
  remove_function_pointers = 3,
  mm_io = 4,
  instrument_preconditions = 5,
  goto_partial_inline = 6,
  remove_returns = 7,
  remove_vector = 8,
  remove_complex = 9,
  rewrite_union = 10,
  transform_assertions_assumptions = 11,
  adjust_float_expressions = 12,
  string_abstraction = 13,
  remove_unused_functions = 14,
  remove_skip = 15,
  label_properties = 16
};

/// Returns true if \param transform is one of the values in the definition of
/// the enumeration above.
bool is_valid_transform_kind(goto_transform_kindt transform);

void add_history_transform(
  goto_transform_kindt transform_kind,
  goto_functiont &function);

void add_history_transform(
  goto_transform_kindt transform_kind,
  goto_functionst &functions);

#endif // CPROVER_GOTO_PROGRAMS_GOTO_TRANSFORM_HISTORY_H
