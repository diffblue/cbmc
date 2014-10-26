/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_SSA_EXPR_H
#define CPROVER_GOTO_SYMEX_SSA_EXPR_H

#include <util/std_expr.h>

/*! \brief Expression providing an SSA-renamed symbol of expressions
*/
class ssa_exprt:public symbol_exprt
{
public:
  inline ssa_exprt()
  {
    set(ID_C_SSA_symbol, true);
  }

  /*! \brief Constructor
   * \param expr Expression to be converted to SSA symbol
  */
  inline explicit ssa_exprt(const exprt &expr):
    symbol_exprt(expr.type())
  {
    set(ID_C_SSA_symbol, true);
    add(ID_expression, expr);
    update_identifier();
  }

  inline const exprt &get_original_expr() const
  {
    return static_cast<const exprt &>(find(ID_expression));
  }

  inline const irep_idt &get_object_name() const
  {
    object_descriptor_exprt ode;
    ode.object()=get_original_expr();
    return to_symbol_expr(ode.root_object()).get_identifier();
  }

  inline const irep_idt get_l1_object_identifier() const
  {
    return build_identifier(
             get_original_expr(),
             get_level_0(),
             get_level_1(),
             irep_idt()); // intentionally blank
  }

  inline const irep_idt get_original_name() const
  {
    ssa_exprt o(get_original_expr());
    return o.get_identifier();
  }

  inline void set_level_0(unsigned i)
  {
    set(ID_L0, i);
    update_identifier();
  }

  inline void set_level_1(unsigned i)
  {
    set(ID_L1, i);
    update_identifier();
  }

  inline void set_level_2(unsigned i)
  {
    set(ID_L2, i);
    update_identifier();
  }

  inline void remove_level_2()
  {
    remove(ID_L2);
    update_identifier();
  }

  inline const irep_idt get_level_0() const
  {
    return get(ID_L0);
  }

  inline const irep_idt get_level_1() const
  {
    return get(ID_L1);
  }

  inline const irep_idt get_level_2() const
  {
    return get(ID_L2);
  }

  void update_identifier()
  {
    const irep_idt &l0=get_level_0();
    const irep_idt &l1=get_level_1();
    const irep_idt &l2=get_level_2();

    set_identifier(build_identifier(get_original_expr(), l0, l1, l2));
  }
  
  static irep_idt build_identifier(
    const exprt &src,
    const irep_idt &l0,
    const irep_idt &l1,
    const irep_idt &l2);
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
extern inline const ssa_exprt &to_ssa_expr(const exprt &expr)
{
  assert(expr.id()==ID_symbol &&
         expr.get_bool(ID_C_SSA_symbol) &&
         !expr.has_operands());
  return static_cast<const ssa_exprt &>(expr);
}

/*! \copydoc to_ssa_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline ssa_exprt &to_ssa_expr(exprt &expr)
{
  assert(expr.id()==ID_symbol &&
         expr.get_bool(ID_C_SSA_symbol) &&
         !expr.has_operands());
  return static_cast<ssa_exprt &>(expr);
}

extern inline bool is_ssa_expr(const exprt &expr)
{
  return expr.id()==ID_symbol &&
         expr.get_bool(ID_C_SSA_symbol);
}

#endif
