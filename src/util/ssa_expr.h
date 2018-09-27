/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_SSA_EXPR_H
#define CPROVER_UTIL_SSA_EXPR_H

#include "std_expr.h"

/*! \brief Expression providing an SSA-renamed symbol of expressions
*/
class ssa_exprt:public symbol_exprt
{
public:
  ssa_exprt()
  {
    set(ID_C_SSA_symbol, true);
  }

  /*! \brief Constructor
   * \param expr Expression to be converted to SSA symbol
  */
  explicit ssa_exprt(const exprt &expr):
    symbol_exprt(expr.type())
  {
    set(ID_C_SSA_symbol, true);
    add(ID_expression, expr);
    update_identifier();
  }

  void update_type()
  {
    static_cast<exprt &>(add(ID_expression)).type()=type();
  }

  const exprt &get_original_expr() const
  {
    return static_cast<const exprt &>(find(ID_expression));
  }

  irep_idt get_object_name() const
  {
    object_descriptor_exprt ode;
    ode.object()=get_original_expr();
    return to_symbol_expr(ode.root_object()).get_identifier();
  }

  const ssa_exprt get_l1_object() const
  {
    object_descriptor_exprt ode;
    ode.object()=get_original_expr();

    ssa_exprt root(ode.root_object());
    root.set(ID_L0, get(ID_L0));
    root.set(ID_L1, get(ID_L1));
    root.update_identifier();

    return root;
  }

  const irep_idt get_l1_object_identifier() const
  {
    #if 0
    return get_l1_object().get_identifier();
    #else
    // the above is the clean version, this is the fast one, using
    // an identifier cached during build_identifier
    return get(ID_L1_object_identifier);
    #endif
  }

  const irep_idt get_original_name() const
  {
    ssa_exprt o(get_original_expr());
    return o.get_identifier();
  }

  void set_level_0(unsigned i)
  {
    set(ID_L0, i);
    update_identifier();
  }

  void set_level_1(unsigned i)
  {
    set(ID_L1, i);
    update_identifier();
  }

  void set_level_2(unsigned i)
  {
    set(ID_L2, i);
    update_identifier();
  }

  void remove_level_2()
  {
    remove(ID_L2);
    update_identifier();
  }

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

  void update_identifier()
  {
    const irep_idt &l0=get_level_0();
    const irep_idt &l1=get_level_1();
    const irep_idt &l2=get_level_2();

    auto idpair=build_identifier(get_original_expr(), l0, l1, l2);
    set_identifier(idpair.first);
    set(ID_L1_object_identifier, idpair.second);
  }

  static std::pair<irep_idt, irep_idt> build_identifier(
    const exprt &src,
    const irep_idt &l0,
    const irep_idt &l1,
    const irep_idt &l2);

  /* Used to determine whether or not an identifier can be built
   * before trying and getting an exception */
  static bool can_build_identifier(const exprt &src);
};

/*! \brief Cast a generic exprt to an \ref ssa_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * ssa_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref ssa_exprt
 *
 * \ingroup gr_std_expr
*/
inline const ssa_exprt &to_ssa_expr(const exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_symbol && expr.get_bool(ID_C_SSA_symbol) &&
    !expr.has_operands());
  return static_cast<const ssa_exprt &>(expr);
}

/*! \copydoc to_ssa_expr(const exprt &)
 * \ingroup gr_std_expr
*/
inline ssa_exprt &to_ssa_expr(exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_symbol && expr.get_bool(ID_C_SSA_symbol) &&
    !expr.has_operands());
  return static_cast<ssa_exprt &>(expr);
}

inline bool is_ssa_expr(const exprt &expr)
{
  return expr.id()==ID_symbol &&
         expr.get_bool(ID_C_SSA_symbol);
}

#endif // CPROVER_UTIL_SSA_EXPR_H
