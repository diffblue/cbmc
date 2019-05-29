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
  /// \param expr: Expression to be converted to SSA symbol
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

  void set_level_0(unsigned i);

  void set_level_1(unsigned i);

  void set_level_2(unsigned i);

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

#endif // CPROVER_UTIL_SSA_EXPR_H
