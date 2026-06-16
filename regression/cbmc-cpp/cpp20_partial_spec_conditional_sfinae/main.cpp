// CORE (N5008 [temp.spec.partial.match]/2, [temp.deduct]/8, [expr.cond]/4).
//
// The same conditional-operator SFINAE partial-spec selection as
// cpp20_partial_spec_conditional_sfinae_member, but exercised with
// function-body locals rather than as members of a class template.  Here CBMC
// is correct: the specialization is selected when a common type exists
// (`cr<int, long>`) and rejected (falling back to the primary) when the
// conditional `decltype` is ill-formed (`cr<int, int*>`).
//
// This is the working contrast to the KNOWNBUG member case, isolating the
// divergence to the class-member-instantiation context.  (CBMC currently also
// leaks a "types are incompatible" diagnostic for the rejected case -- a
// contained substitution failure should be silent per [temp.deduct]/8 -- but
// the verification result itself is correct.)

template <class X>
X declval();

template <class...>
using void_t = void;

template <class A, class B, class = void>
struct cr
{
  int tag = 1; // primary
};

template <class A, class B>
struct cr<A, B, void_t<decltype(false ? declval<A>() : declval<B>())>>
{
  int tag = 2; // selected iff A and B have a common type
};

int main()
{
  cr<int, long> ok;   // common type exists -> specialization (tag 2)
  cr<int, int *> bad; // no common type -> primary (tag 1)
  __CPROVER_assert(ok.tag == 2, "common type -> specialization");
  __CPROVER_assert(bad.tag == 1, "no common type -> primary");
  return 0;
}
