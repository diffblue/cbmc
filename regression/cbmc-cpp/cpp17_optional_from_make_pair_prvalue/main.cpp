// C++17: copy-initializing a std::optional<T> directly from the
// prvalue result of a function-template call (here std::make_pair),
// e.g. `return std::make_pair(1, 2);` into an
// `std::optional<std::pair<int,int>>` return type.
//
// std::make_pair takes its arguments by forwarding reference
// (`_T1&&`).  A prvalue argument (`1`) is bound to that rvalue
// reference by temporary materialization ([conv.rval],
// [class.temporary]): the prvalue becomes a glvalue denoting a
// materialized temporary object, which the front end represents as a
// `temporary_object` side effect whose address is taken to pass it by
// reference.  The resulting (already-typechecked) make_pair call thus
// internally contains `address_of(temporary_object(1))`.
//
// Converting that call's prvalue result into the optional uses
// optional's converting constructor template `optional(_Up&&)`, which
// `cpp_constructor` resolves by RE-TYPECHECKING the call expression.
// The address-of typecheck rejected the materialized
// `temporary_object` as a non-lvalue ("address_of error: ... not an
// lvalue"), so the constructor was dropped and the conversion failed
// with "invalid implicit conversion from 'struct pair' to 'struct
// optional'".  Binding the prvalue argument via a *named* temporary
// (`auto t = ...; make_pair(t, ...)`) or returning a plain function's
// pair prvalue both worked, isolating the failure to the
// materialized-temporary argument of make_pair.
//
// Per [conv.rval]/[class.temporary] a materialized temporary is a
// glvalue denoting an object that has storage, so its address may be
// taken; the fix makes the address-of typecheck treat a
// `temporary_object` as an lvalue, which also makes re-typechecking
// such a call idempotent.
//
// CBMC's own `c_types.cpp` hits this when returning
//   std::make_pair(struct_union_typet::componentt{...}, *max_width)
// into an `std::optional<std::pair<componentt, mp_integer>>`.
//
// Verified at the goto-program level (full BMC of std::optional
// exceeds symex memory limits): the goto program must show the
// converting constructor invoked with the make_pair temporary, and
// must NOT report the conversion error.

#include <optional>
#include <utility>

std::optional<std::pair<int, int>> make_opt_pair()
{
  return std::make_pair(1, 2);
}

int main()
{
  return make_opt_pair().has_value() ? 0 : 1;
}
