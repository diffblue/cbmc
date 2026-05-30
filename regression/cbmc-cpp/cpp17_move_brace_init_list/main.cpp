// Regression for [expr.call] re-entrant typecheck of a function call
// returning an rvalue reference.
//
// When `cpp_constructor`'s operand loop calls `typecheck_expr(op)` on
// an existing `*move(...)` and the operand walk descends back into
// the inner side-effect-call,
// `typecheck_side_effect_function_call` would re-process the call
// and call `add_implicit_dereference(expr)` at the tail again,
// wrapping the call in a SECOND `*`.  The parent dereference's
// operand then becomes `*call(...)` instead of `call(...)`, and
// `typecheck_expr_dereference` rejects it as
//
//     operand of unary * is not a pointer, but got 'struct T'
//
// surfacing in libstdc++ chains as
//
//     *move<ref_struct_tag(identifier=tag-X)>(...)
//
// is not a pointer.  This broke every CBMC source file using the
// `multi_ary_exprt(_id, std::move(_type), {std::move(_op0), ...})`
// pattern.

#include <utility>

struct expr_t
{
  int x;
};

void take_by_value(expr_t e)
{
  (void)e;
}

void take_rvalue_ref(expr_t &&e)
{
  (void)e;
}

int main()
{
  expr_t a;
  // Direct move into a function taking the rvalue-reference: the
  // call `std::move(a)` is type-checked once, wrapped in `*` by
  // `add_implicit_dereference`, and the wrapped form is later
  // re-typechecked when the temporary copy materialises.
  take_by_value(std::move(a));
  // Same for a function taking T&& directly.
  take_rvalue_ref(std::move(a));
  return 0;
}
