/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_SSA_EXPR_H
#define CPROVER_UTIL_SSA_EXPR_H

#include "std_expr.h"

/// Expression providing an SSA-renamed symbol of expressions
class ssa_exprt:public symbol_exprt
{
public:
  /// Constructor
  /// \param expr: Expression to be converted to SSA symbol. A valid argument
  ///   must be one of these:
  ///   - a symbol_exprt
  ///   - a member_exprt where the accessed struct would be a valid argument
  ///   - an index_exprt where the index is a constant and the array would be
  ///     a valid argument
  explicit ssa_exprt(const exprt &expr);

  void update_type()
  {
    static_cast<exprt &>(add(ID_expression)).type()=type();
  }

  const exprt &get_original_expr() const
  {
    return static_cast<const exprt &>(find(ID_expression));
  }

  /// Replace the underlying, original expression by \p expr while maintaining
  /// SSA indices.
  /// \param expr: expression to store
  void set_expression(const exprt &expr);

  irep_idt get_object_name() const;

  const ssa_exprt get_l1_object() const;

  const irep_idt get_l1_object_identifier() const;

  const irep_idt get_original_name() const
  {
    ssa_exprt o(get_original_expr());
    return o.get_identifier();
  }

  void set_level_0(std::size_t i);

  void set_level_1(std::size_t i);

  void set_level_2(std::size_t i);

  void remove_level_2();

  const irep_idt get_level_0() const
  {
    return get(ID_L0);
  }

  const irep_idt get_level_1() const
  {
    return get(ID_L1);
  }

  const irep_idt get_level_2() const
  {
    return get(ID_L2);
  }

  DEPRECATED(SINCE(2019, 05, 29, "Should only be used internally"))
  void update_identifier();

  /// Used to determine whether or not an identifier can be built before trying
  /// and getting an exception
  static bool can_build_identifier(const exprt &src);

  static void check(
    const exprt &expr,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm, !expr.has_operands(), "SSA expression should not have operands");
    DATA_CHECK(
      vm, expr.id() == ID_symbol, "SSA expression symbols are symbols");
    DATA_CHECK(vm, expr.get_bool(ID_C_SSA_symbol), "wrong SSA expression ID");
    // Check that each of the L0, L1 and L2 indices are either absent or are
    // set to a non-empty value -- otherwise we could have two ssa_exprts that
    // represent the same value (since get(ID_L0/1/2) will yield an empty string
    // in both cases), but which do not compare equal (since irept::compare
    // does not regard a missing key and an empty value as equivalent)
    const auto &expr_sub = expr.get_named_sub();
    const auto expr_l0 = expr_sub.find(ID_L0);
    const auto expr_l1 = expr_sub.find(ID_L1);
    const auto expr_l2 = expr_sub.find(ID_L2);
    DATA_CHECK(
      vm,
      expr_l0 == expr_sub.end() || !expr_l0->second.id().empty(),
      "L0 must not be an empty string");
    DATA_CHECK(
      vm,
      expr_l1 == expr_sub.end() || !expr_l1->second.id().empty(),
      "L1 must not be an empty string");
    DATA_CHECK(
      vm,
      expr_l2 == expr_sub.end() || !expr_l2->second.id().empty(),
      "L2 must not be an empty string");
  }

  static void validate(
    const exprt &expr,
    const namespacet &ns,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    check(expr, vm);
    validate_full_expr(
      static_cast<const exprt &>(expr.find(ID_expression)), ns, vm);
  }
};

inline bool is_ssa_expr(const exprt &expr)
{
  return expr.id() == ID_symbol && expr.get_bool(ID_C_SSA_symbol);
}

template <>
inline bool can_cast_expr<ssa_exprt>(const exprt &base)
{
  return is_ssa_expr(base);
}

inline void validate_expr(const ssa_exprt &expr)
{
  ssa_exprt::check(expr);
}

/// Cast a generic exprt to an \ref ssa_exprt.
/// \param expr: Source expression
/// \return Object of type \ref ssa_exprt
/// \ingroup gr_std_expr
inline const ssa_exprt &to_ssa_expr(const exprt &expr)
{
  ssa_exprt::check(expr);
  return static_cast<const ssa_exprt &>(expr);
}

/// \copydoc to_ssa_expr(const exprt &)
/// \ingroup gr_std_expr
inline ssa_exprt &to_ssa_expr(exprt &expr)
{
  ssa_exprt::check(expr);
  return static_cast<ssa_exprt &>(expr);
}

/// \return copy of \p ssa where level2 identifiers have been removed
ssa_exprt remove_level_2(ssa_exprt ssa);

#endif // CPROVER_UTIL_SSA_EXPR_H
