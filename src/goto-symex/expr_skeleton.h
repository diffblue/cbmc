/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Expression skeleton

#ifndef CPROVER_GOTO_SYMEX_EXPR_SKELETON_H
#define CPROVER_GOTO_SYMEX_EXPR_SKELETON_H

#include <util/expr.h>
#include <util/mp_arith.h>

/// Expression in which some part is missing and can be substituted for another
/// expression.
///
/// For instance, a skeleton `☐[index]` where `☐` is the missing part, can be
/// applied to an expression `x` to get `x[index]` (see
/// \ref expr_skeletont::apply). It can also be composed with another skeleton,
/// let say `☐.some_field` which would give the skeleton `☐.some_field[index]`
/// (see \ref expr_skeletont::compose).
class expr_skeletont final
{
public:
  /// Empty skeleton. Applying it to an expression would give the same
  /// expression unchanged
  explicit expr_skeletont(typet missing_type);

  /// Replace the missing part of the current skeleton by another skeleton,
  /// ending in a bigger skeleton corresponding to the two combined.
  expr_skeletont compose(expr_skeletont other) const;

  /// Replace the missing part by the given expression, to end-up with a
  /// complete expression
  exprt apply(exprt expr) const;

  /// Create a skeleton by removing the first operand of \p e. For instance,
  /// remove_op0 on `array[index]` would give a skeleton in which `array` is
  /// missing, and applying that skeleton to `array2` would give
  /// `array2[index]`.
  static expr_skeletont remove_op0(exprt e);

  /// If the deepest subexpression in the skeleton is a member expression,
  /// replace it with a nil expression and return the obtained skeleton.
  static optionalt<expr_skeletont>
  clear_innermost_index_expr(expr_skeletont skeleton);

  /// If the deepest subexpression in the skeleton is a member expression,
  /// replace it with a nil expression and return the obtained skeleton.
  static optionalt<expr_skeletont>
  clear_innermost_member_expr(expr_skeletont skeleton);

  /// If the deepest subexpression in the skeleton is a byte-extract expression,
  /// replace it with a nil expression and return the obtained skeleton.
  /// For instance, for `(byte_extract(☐, 2, int)).field[index]`
  /// `☐.field[index]` is returned, while for `byte_extract(☐.field, 2, int)`
  /// an empty optional is returned.
  static optionalt<expr_skeletont>
  clear_innermost_byte_extract_expr(expr_skeletont skeleton);

  /// Attempt to return a skeleton `s` such that for all expression \c x,
  /// `s.apply(byte_extract(x, offset, type))` would be semantically equivalent
  /// to `skeleton.apply(x)`.
  /// If offset + type size exceeds the size (in bytes) of the skeleton then
  /// an empty optional is returned.
  /// This is done by removing operations of the skeleton (starting by the
  /// deepest ones), until the accumulated offset match or exceed \p offset.
  /// If it does not exactly match then one of the operation will be replaced
  /// by a byte_extract.
  static expr_skeletont revert_byte_extract(
    expr_skeletont skeleton,
    exprt offset,
    const typet &type,
    const namespacet &ns);

private:
  /// In \c skeleton, nil_exprt is used to mark the sub expression to be
  /// substituted. The nil_exprt always appears recursively following the first
  /// operands because the only way to get a skeleton is by removing the first
  /// operand.
  exprt skeleton;
  typet type_of_missing_part;

  expr_skeletont(exprt e, typet missing)
    : skeleton(std::move(e)), type_of_missing_part(std::move(missing))
  {
  }

  /// Auxiliary function for revert_byte_extract.
  /// It is recursive and has an extra argument for keeping track of the offset
  /// that has been removed by the recursive calls.
  static expr_skeletont revert_byte_extract_aux(
    expr_skeletont skeleton,
    exprt offset,
    const typet &type,
    const namespacet &ns,
    exprt offset_already_removed);
};

#endif // CPROVER_GOTO_SYMEX_EXPR_SKELETON_H
