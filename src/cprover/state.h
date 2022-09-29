/*******************************************************************\

Module: State Encoding

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_CPROVER_STATE_H
#define CPROVER_CPROVER_STATE_H

#include <util/mathematical_expr.h>
#include <util/pointer_expr.h>

class state_typet : public typet
{
public:
  state_typet() : typet(ID_state)
  {
  }
};

static inline mathematical_function_typet state_predicate_type()
{
  return mathematical_function_typet({state_typet()}, bool_typet());
}

static inline symbol_exprt state_expr()
{
  return symbol_exprt(u8"\u03c2", state_typet());
}

class initial_state_exprt : public unary_predicate_exprt
{
public:
  explicit initial_state_exprt(exprt state)
    : unary_predicate_exprt(ID_initial_state, std::move(state))
  {
    PRECONDITION(this->state().type().id() == ID_state);
  }

  const exprt &state() const
  {
    return op();
  }

  exprt &state()
  {
    return op();
  }
};

/// \brief Cast an exprt to a \ref initial_state_exprt
///
/// \a expr must be known to be \ref initial_state_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref initial_state_exprt
inline const initial_state_exprt &to_initial_state_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_initial_state);
  const initial_state_exprt &ret =
    static_cast<const initial_state_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_initial_state_expr(const exprt &)
inline initial_state_exprt &to_initial_state_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_initial_state);
  initial_state_exprt &ret = static_cast<initial_state_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class evaluate_exprt : public binary_exprt
{
public:
  evaluate_exprt(exprt state, exprt address, typet type)
    : binary_exprt(
        std::move(state),
        ID_evaluate,
        std::move(address),
        std::move(type))
  {
    PRECONDITION(this->state().type().id() == ID_state);
    PRECONDITION(this->address().type().id() == ID_pointer);
  }

  // convenience constructor
  evaluate_exprt(exprt state, exprt address)
    : evaluate_exprt(
        std::move(state),
        address,
        to_pointer_type(address.type()).base_type())
  {
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }

  // helper
  evaluate_exprt with_state(exprt state) const
  {
    auto result = *this; // copy
    result.state() = std::move(state);
    return result;
  }
};

/// \brief Cast an exprt to a \ref evaluate_exprt
///
/// \a expr must be known to be \ref evaluate_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref evaluate_exprt
inline const evaluate_exprt &to_evaluate_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_evaluate);
  const evaluate_exprt &ret = static_cast<const evaluate_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_evaluate_expr(const exprt &)
inline evaluate_exprt &to_evaluate_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_evaluate);
  evaluate_exprt &ret = static_cast<evaluate_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class update_state_exprt : public ternary_exprt
{
public:
  update_state_exprt(exprt state, exprt address, exprt new_value)
    : ternary_exprt(
        ID_update_state,
        std::move(state),
        std::move(address),
        std::move(new_value),
        state_typet())
  {
    PRECONDITION(this->state().type().id() == ID_state);
    PRECONDITION(this->address().type().id() == ID_pointer);
    PRECONDITION(
      to_pointer_type(this->address().type()).base_type() ==
      this->new_value().type());
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }

  const exprt &new_value() const
  {
    return op2();
  }

  // helper
  update_state_exprt with_state(exprt state) const
  {
    auto result = *this; // copy
    result.state() = std::move(state);
    return result;
  }
};

/// \brief Cast an exprt to a \ref update_state_exprt
///
/// \a expr must be known to be \ref update_state_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref update_state_exprt
inline const update_state_exprt &to_update_state_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_update_state);
  const update_state_exprt &ret = static_cast<const update_state_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_update_state_expr(const exprt &)
inline update_state_exprt &to_update_state_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_update_state);
  update_state_exprt &ret = static_cast<update_state_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class allocate_exprt : public binary_exprt
{
public:
  allocate_exprt(exprt state, exprt size, pointer_typet type)
    : binary_exprt(
        std::move(state),
        ID_allocate,
        std::move(size),
        std::move(type))
  {
    PRECONDITION(this->state().type().id() == ID_state);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &size() const
  {
    return op1();
  }

  // helper
  allocate_exprt with_state(exprt state) const
  {
    auto result = *this; // copy
    result.state() = std::move(state);
    return result;
  }
};

/// \brief Cast an exprt to a \ref allocate_exprt
///
/// \a expr must be known to be \ref allocate_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref allocate_exprt
inline const allocate_exprt &to_allocate_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_allocate);
  const allocate_exprt &ret = static_cast<const allocate_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class allocate_state_exprt : public binary_exprt
{
public:
  allocate_state_exprt(exprt state, exprt size)
    : binary_exprt(
        std::move(state),
        ID_allocate_state,
        std::move(size),
        state_typet())
  {
    PRECONDITION(this->state().type().id() == ID_state);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &size() const
  {
    return op1();
  }
};

/// \brief Cast an exprt to a \ref allocate_state_exprt
///
/// \a expr must be known to be \ref allocate_state_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref allocate_state_exprt
inline const allocate_state_exprt &to_allocate_state_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_allocate_state);
  const allocate_state_exprt &ret =
    static_cast<const allocate_state_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class reallocate_exprt : public ternary_exprt
{
public:
  reallocate_exprt(exprt state, exprt address, exprt size, pointer_typet type)
    : ternary_exprt(
        ID_reallocate,
        std::move(state),
        std::move(address),
        std::move(size),
        std::move(type))
  {
    PRECONDITION(this->state().type().id() == ID_state);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }

  const exprt &size() const
  {
    return op2();
  }
};

/// \brief Cast an exprt to a \ref reallocate_exprt
///
/// \a expr must be known to be \ref reallocate_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref allocate_exprt
inline const reallocate_exprt &to_reallocate_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_reallocate);
  const reallocate_exprt &ret = static_cast<const reallocate_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class reallocate_state_exprt : public ternary_exprt
{
public:
  reallocate_state_exprt(exprt state, exprt address, exprt size)
    : ternary_exprt(
        ID_allocate_state,
        std::move(state),
        std::move(address),
        std::move(size),
        state_typet())
  {
    PRECONDITION(this->state().type().id() == ID_state);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }

  const exprt &size() const
  {
    return op1();
  }
};

/// \brief Cast an exprt to a \ref reallocate_state_exprt
///
/// \a expr must be known to be \ref reallocate_state_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref reallocate_state_exprt
inline const reallocate_state_exprt &to_reallocate_state_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_reallocate_state);
  const reallocate_state_exprt &ret =
    static_cast<const reallocate_state_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class deallocate_state_exprt : public binary_exprt
{
public:
  deallocate_state_exprt(exprt state, exprt address)
    : binary_exprt(
        std::move(state),
        ID_deallocate_state,
        std::move(address),
        state_typet())
  {
    PRECONDITION(this->state().type().id() == ID_state);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }
};

/// \brief Cast an exprt to a \ref deallocate_state_exprt
///
/// \a expr must be known to be \ref deallocate_state_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref deallocate_state_exprt
inline const deallocate_state_exprt &to_deallocate_state_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_deallocate_state);
  const deallocate_state_exprt &ret =
    static_cast<const deallocate_state_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class state_live_object_exprt : public binary_predicate_exprt
{
public:
  state_live_object_exprt(exprt state, exprt address)
    : binary_predicate_exprt(
        std::move(state),
        ID_state_live_object,
        std::move(address))
  {
    PRECONDITION(this->state().type().id() == ID_state);
    PRECONDITION(this->address().type().id() == ID_pointer);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }

  // helper
  state_live_object_exprt with_state(exprt state) const
  {
    auto result = *this; // copy
    result.state() = std::move(state);
    return result;
  }
};

/// \brief Cast an exprt to a \ref state_live_object_exprt
///
/// \a expr must be known to be \ref state_live_object_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref state_live_object_exprt
inline const state_live_object_exprt &
to_state_live_object_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_state_live_object);
  const state_live_object_exprt &ret =
    static_cast<const state_live_object_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_state_live_object_expr(const exprt &)
inline state_live_object_exprt &to_state_live_object_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_state_live_object);
  state_live_object_exprt &ret = static_cast<state_live_object_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class state_writeable_object_exprt : public binary_predicate_exprt
{
public:
  state_writeable_object_exprt(exprt state, exprt address)
    : binary_predicate_exprt(
        std::move(state),
        ID_state_writeable_object,
        std::move(address))
  {
    PRECONDITION(this->state().type().id() == ID_state);
    PRECONDITION(this->address().type().id() == ID_pointer);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }
};

/// \brief Cast an exprt to a \ref state_writeable_object_exprt
///
/// \a expr must be known to be \ref state_writeable_object_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref state_writeable_object_exprt
inline const state_writeable_object_exprt &
to_state_writeable_object_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_state_writeable_object);
  const state_writeable_object_exprt &ret =
    static_cast<const state_writeable_object_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_state_writeable_object_expr(const exprt &)
inline state_writeable_object_exprt &to_state_writeable_object_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_state_writeable_object);
  state_writeable_object_exprt &ret =
    static_cast<state_writeable_object_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class state_is_cstring_exprt : public binary_predicate_exprt
{
public:
  state_is_cstring_exprt(exprt state, exprt address)
    : binary_predicate_exprt(
        std::move(state),
        ID_state_is_cstring,
        std::move(address))
  {
    PRECONDITION(this->state().type().id() == ID_state);
    PRECONDITION(this->address().type().id() == ID_pointer);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }

  // helper
  state_is_cstring_exprt with_state(exprt state) const
  {
    auto result = *this; // copy
    result.state() = std::move(state);
    return result;
  }
};

/// \brief Cast an exprt to a \ref state_is_cstring_exprt
///
/// \a expr must be known to be \ref state_is_cstring_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref state_is_cstring_exprt
inline const state_is_cstring_exprt &to_state_is_cstring_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_state_is_cstring);
  const state_is_cstring_exprt &ret =
    static_cast<const state_is_cstring_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_state_is_cstring_expr(const exprt &)
inline state_is_cstring_exprt &to_state_is_cstring_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_state_is_cstring);
  state_is_cstring_exprt &ret = static_cast<state_is_cstring_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class state_cstrlen_exprt : public binary_exprt
{
public:
  state_cstrlen_exprt(exprt state, exprt address, typet type)
    : binary_exprt(
        std::move(state),
        ID_state_cstrlen,
        std::move(address),
        std::move(type))
  {
    PRECONDITION(this->state().type().id() == ID_state);
    PRECONDITION(this->address().type().id() == ID_pointer);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }

  // helper
  state_cstrlen_exprt with_state(exprt state) const
  {
    auto result = *this; // copy
    result.state() = std::move(state);
    return result;
  }
};

/// \brief Cast an exprt to a \ref state_cstrlen_exprt
///
/// \a expr must be known to be \ref state_cstrlen_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref state_cstrlen_exprt
inline const state_cstrlen_exprt &to_state_cstrlen_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_state_cstrlen);
  const state_cstrlen_exprt &ret =
    static_cast<const state_cstrlen_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_state_cstrlen_expr(const exprt &)
inline state_cstrlen_exprt &to_state_cstrlen_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_state_cstrlen);
  state_cstrlen_exprt &ret = static_cast<state_cstrlen_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class state_is_dynamic_object_exprt : public binary_predicate_exprt
{
public:
  state_is_dynamic_object_exprt(exprt state, exprt address)
    : binary_predicate_exprt(
        std::move(state),
        ID_state_is_dynamic_object,
        std::move(address))
  {
    PRECONDITION(this->state().type().id() == ID_state);
    PRECONDITION(this->address().type().id() == ID_pointer);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }

  // helper
  state_is_dynamic_object_exprt with_state(exprt state) const
  {
    auto result = *this; // copy
    result.state() = std::move(state);
    return result;
  }
};

/// \brief Cast an exprt to a \ref state_is_dynamic_object_exprt
///
/// \a expr must be known to be \ref state_is_dynamic_object_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref state_is_dynamic_object_exprt
inline const state_is_dynamic_object_exprt &
to_state_is_dynamic_object_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_state_is_dynamic_object);
  const state_is_dynamic_object_exprt &ret =
    static_cast<const state_is_dynamic_object_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_state_is_dynamic_object_expr(const exprt &)
inline state_is_dynamic_object_exprt &
to_state_is_dynamic_object_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_state_is_dynamic_object);
  state_is_dynamic_object_exprt &ret =
    static_cast<state_is_dynamic_object_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class state_object_size_exprt : public binary_exprt
{
public:
  state_object_size_exprt(exprt state, exprt address, typet type)
    : binary_exprt(
        std::move(state),
        ID_state_object_size,
        std::move(address),
        std::move(type))
  {
    PRECONDITION(this->state().type().id() == ID_state);
    PRECONDITION(this->address().type().id() == ID_pointer);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }

  // helper
  state_object_size_exprt with_state(exprt state) const
  {
    auto result = *this; // copy
    result.state() = std::move(state);
    return result;
  }
};

/// \brief Cast an exprt to a \ref state_object_size_exprt
///
/// \a expr must be known to be \ref state_object_size_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref state_object_size_exprt
inline const state_object_size_exprt &
to_state_object_size_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_state_object_size);
  const state_object_size_exprt &ret =
    static_cast<const state_object_size_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_state_object_size_expr(const exprt &)
inline state_object_size_exprt &to_state_object_size_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_state_object_size);
  state_object_size_exprt &ret = static_cast<state_object_size_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class state_ok_exprt : public ternary_exprt
{
public:
  state_ok_exprt(irep_idt id, exprt state, exprt address, exprt size)
    : ternary_exprt(
        id,
        std::move(state),
        std::move(address),
        std::move(size),
        bool_typet())
  {
    PRECONDITION(this->state().type().id() == ID_state);
    PRECONDITION(this->address().type().id() == ID_pointer);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }

  exprt &address()
  {
    return op1();
  }

  const exprt &size() const
  {
    return op2();
  }

  exprt &size()
  {
    return op2();
  }

  // helper
  state_ok_exprt with_state(exprt state) const
  {
    auto result = *this; // copy
    result.state() = std::move(state);
    return result;
  }
};

/// \brief Cast an exprt to a \ref state_ok_exprt
///
/// \a expr must be known to be \ref state_ok_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref state_ok_exprt
inline const state_ok_exprt &to_state_ok_expr(const exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_state_r_ok || expr.id() == ID_state_w_ok ||
    expr.id() == ID_state_rw_ok);
  const state_ok_exprt &ret = static_cast<const state_ok_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_state_ok_expr(const exprt &)
inline state_ok_exprt &to_state_ok_expr(exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_state_r_ok || expr.id() == ID_state_w_ok ||
    expr.id() == ID_state_rw_ok);
  state_ok_exprt &ret = static_cast<state_ok_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class state_type_compatible_exprt : public binary_exprt
{
public:
  state_type_compatible_exprt(exprt state, exprt address)
    : binary_exprt(
        std::move(state),
        ID_state_type_compatible,
        std::move(address),
        bool_typet())
  {
    PRECONDITION(this->state().type().id() == ID_state);
    PRECONDITION(this->address().type().id() == ID_pointer);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }

  exprt &address()
  {
    return op1();
  }

  const typet &access_type() const
  {
    return to_pointer_type(address().type()).base_type();
  }

  // helper
  state_type_compatible_exprt with_state(exprt state) const
  {
    auto result = *this; // copy
    result.state() = std::move(state);
    return result;
  }
};

/// \brief Cast an exprt to a \ref state_type_compatible_exprt
///
/// \a expr must be known to be \ref state_type_compatible_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref state_type_compatible_exprt
inline const state_type_compatible_exprt &
to_state_type_compatible_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_state_type_compatible);
  const state_type_compatible_exprt &ret =
    static_cast<const state_type_compatible_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_state_type_compatible_expr(const exprt &)
inline state_type_compatible_exprt &to_state_type_compatible_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_state_type_compatible);
  state_type_compatible_exprt &ret =
    static_cast<state_type_compatible_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class enter_scope_state_exprt : public binary_exprt
{
public:
  enter_scope_state_exprt(exprt state, exprt address)
    : binary_exprt(
        std::move(state),
        ID_enter_scope_state,
        std::move(address),
        state_typet())
  {
    PRECONDITION(this->state().type().id() == ID_state);
    PRECONDITION(this->address().type().id() == ID_pointer);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }

  exprt &address()
  {
    return op1();
  }

  typet object_type() const
  {
    return to_pointer_type(address().type()).base_type();
  }

  symbol_exprt symbol() const
  {
    PRECONDITION(address().id() == ID_object_address);
    return to_object_address_expr(address()).object_expr();
  }

#if 0
  const exprt &size() const
  {
    return op2();
  }

  exprt &size()
  {
    return op2();
  }
#endif
};

/// \brief Cast an exprt to a \ref enter_scope_state_exprt
///
/// \a expr must be known to be \ref enter_scope_state_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref enter_scope_state_exprt
inline const enter_scope_state_exprt &
to_enter_scope_state_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_enter_scope_state);
  const enter_scope_state_exprt &ret =
    static_cast<const enter_scope_state_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_enter_scope_state_expr(const exprt &)
inline enter_scope_state_exprt &to_enter_scope_state_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_enter_scope_state);
  enter_scope_state_exprt &ret = static_cast<enter_scope_state_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class exit_scope_state_exprt : public binary_exprt
{
public:
  exit_scope_state_exprt(exprt state, exprt address)
    : binary_exprt(
        std::move(state),
        ID_exit_scope_state,
        std::move(address),
        state_typet())
  {
    PRECONDITION(this->state().type().id() == ID_state);
    PRECONDITION(this->address().type().id() == ID_pointer);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }

  exprt &address()
  {
    return op1();
  }

  symbol_exprt symbol() const
  {
    PRECONDITION(address().id() == ID_object_address);
    return to_object_address_expr(address()).object_expr();
  }

#if 0
  const exprt &size() const
  {
    return op2();
  }

  exprt &size()
  {
    return op2();
  }
#endif
};

/// \brief Cast an exprt to a \ref exit_scope_state_exprt
///
/// \a expr must be known to be \ref exit_scope_state_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref exit_scope_state_exprt
inline const exit_scope_state_exprt &to_exit_scope_state_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_exit_scope_state);
  const exit_scope_state_exprt &ret =
    static_cast<const exit_scope_state_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_exit_scope_state_expr(const exprt &)
inline exit_scope_state_exprt &to_exit_scope_state_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_exit_scope_state);
  exit_scope_state_exprt &ret = static_cast<exit_scope_state_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

#endif // CPROVER_CPROVER_STATE_H
