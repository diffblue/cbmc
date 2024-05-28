/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_FLATTENING_LITERAL_VECTOR_EXPR_H
#define CPROVER_SOLVERS_FLATTENING_LITERAL_VECTOR_EXPR_H

#include <util/std_expr.h>
#include <util/string2int.h>

#include <solvers/prop/literal.h>

class literal_vector_exprt : public nullary_exprt
{
public:
  literal_vector_exprt(const bvt &__bv, typet __type)
    : nullary_exprt(ID_literal_vector, std::move(__type))
  {
    bv(__bv);
  }

  bvt bv() const
  {
    auto &sub = find(ID_literals).get_sub();
    bvt result;
    result.reserve(sub.size());
    for(auto &literal_irep : sub)
    {
      literalt l;
      l.set(literalt::var_not(
        unsafe_string2signedlonglong(literal_irep.id_string())));
      result.push_back(l);
    }
    return result;
  }

  void bv(const bvt &bv)
  {
    auto &sub = add(ID_literals).get_sub();
    sub.clear();
    sub.reserve(bv.size());
    for(auto &literal : bv)
      sub.emplace_back(irept{std::to_string(literal.get())});
  }
};

template <>
inline bool can_cast_expr<literal_vector_exprt>(const exprt &base)
{
  return base.id() == ID_literal_vector;
}

/// Cast a generic exprt to a \ref literal_vector_exprt. This is an unchecked
/// conversion. \a expr must be known to be \ref literal_vector_exprt.
/// \param expr: Source expression
/// \return Object of type \ref literal_vector_exprt
/// \ingroup gr_std_expr
inline const literal_vector_exprt &to_literal_vector_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_literal_vector);
  literal_vector_exprt::check(expr);
  return static_cast<const literal_vector_exprt &>(expr);
}

/// \copydoc to_literal_expr(const exprt &)
/// \ingroup gr_std_expr
inline literal_vector_exprt &to_literal_vector_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_literal_vector);
  literal_vector_exprt::check(expr);
  return static_cast<literal_vector_exprt &>(expr);
}

#endif // CPROVER_SOLVERS_FLATTENING_LITERAL_VECTOR_EXPR_H
