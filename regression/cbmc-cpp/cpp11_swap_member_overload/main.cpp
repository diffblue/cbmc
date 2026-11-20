// Regression test for the forward-declaration -> definition resolution of an
// overloaded function template in instantiate_template.
//
// std::swap has several overloads that share the base name `swap` but differ
// in their template parameter lists: the generic swap(_Tp&,_Tp&) (one type
// parameter) and the pair swap(pair<_T1,_T2>&, ...) (two type parameters).
// When the deduced winner (generic swap, resolved from a forward declaration)
// was matched to a definition by base name alone, it could bind the pair
// overload's two-parameter list to the single deduced argument, leaving a
// template parameter unbound; the pair signature's `pair<_T1,_T2>` then threw
// on the unbound parameter and the enclosing method body was silently dropped
// (an unsound no-op).  With the signature-matching fix the correct generic
// overload is instantiated and swap of a struct-member lvalue works.
//
// Non-vacuous: the asserted post-swap values are only correct if swap_self's
// body is actually present and the swap really executes.
#include <utility>

struct S
{
  unsigned a;
  void swap_self(S &other)
  {
    std::swap(a, other.a);
  }
};

int main()
{
  S x, y;
  x.a = 1;
  y.a = 2;
  x.swap_self(y);
  __CPROVER_assert(x.a == 2, "member swap: x takes y's value");
  __CPROVER_assert(y.a == 1, "member swap: y takes x's value");
  return 0;
}
