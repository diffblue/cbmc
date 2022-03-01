/*******************************************************************\

Module: Sentinel Doubly Linked Lists

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_CPROVER_SENTINEL_DLL_H
#define CPROVER_CPROVER_SENTINEL_DLL_H

#include <util/std_expr.h>

class state_is_sentinel_dll_exprt : public multi_ary_exprt
{
public:
  state_is_sentinel_dll_exprt(exprt state, exprt head, exprt tail)
    : multi_ary_exprt(
        ID_state_is_sentinel_dll,
        {state, head, tail},
        bool_typet())
  {
    PRECONDITION(this->state().type().id() == ID_state);
    PRECONDITION(this->head().type().id() == ID_pointer);
    PRECONDITION(this->tail().type().id() == ID_pointer);
  }

  state_is_sentinel_dll_exprt(exprt state, exprt head, exprt tail, exprt node)
    : multi_ary_exprt(
        ID_state_is_sentinel_dll,
        {state, head, tail, node},
        bool_typet())
  {
    PRECONDITION(this->state().type().id() == ID_state);
    PRECONDITION(this->head().type().id() == ID_pointer);
    PRECONDITION(this->tail().type().id() == ID_pointer);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &head() const
  {
    return op1();
  }

  exprt &head()
  {
    return op1();
  }

  const exprt &tail() const
  {
    return op2();
  }

  exprt &tail()
  {
    return op2();
  }

  // helper
  state_is_sentinel_dll_exprt with_state(exprt state) const
  {
    auto result = *this; // copy
    result.state() = std::move(state);
    return result;
  }
};

/// \brief Cast an exprt to a \ref state_is_sentinel_dll_exprt
///
/// \a expr must be known to be \ref state_is_sentinel_dll_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref state_is_sentinel_dll_exprt
inline const state_is_sentinel_dll_exprt &
to_state_is_sentinel_dll_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_state_is_sentinel_dll);
  const state_is_sentinel_dll_exprt &ret =
    static_cast<const state_is_sentinel_dll_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_state_is_sentinel_dll_expr(const exprt &)
inline state_is_sentinel_dll_exprt &to_state_is_sentinel_dll_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_state_is_sentinel_dll);
  state_is_sentinel_dll_exprt &ret =
    static_cast<state_is_sentinel_dll_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

optionalt<exprt>
sentinel_dll_next(const exprt &state, const exprt &node, const namespacet &);

optionalt<exprt>
sentinel_dll_prev(const exprt &state, const exprt &node, const namespacet &);

#endif // CPROVER_CPROVER_SENTINEL_DLL_H
