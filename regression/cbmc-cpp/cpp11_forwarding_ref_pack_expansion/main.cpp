// N5008 [temp.variadic]/5, [dcl.ref] (reference collapsing): expanding a
// FORWARDING-REFERENCE parameter pack `A&&... a` in a function-call argument
// pattern `f(static_cast<A&&>(a)...)` (i.e. `f(std::forward<A>(a)...)`) must
// produce, for each element k, the argument `static_cast<A_k&&>(a$k)` with the
// k-th deduced type substituted in lockstep with the k-th expanded value
// parameter.  This is the body of libstdc++'s variadic `std::__invoke`.
//
// KNOWN BUG: the body pack expander handles a bare value-pack call argument
// (`f(a...)`) but not a pattern argument that merely *contains* the pack
// (`f(static_cast<A&&>(a)...)`); the type pack `A` is not substituted in
// lockstep, so the forwarded arguments carry the wrong type/value and the call
// computes the wrong result.  A by-value pack (`f(a...)`) and non-pack
// forwarding-reference arguments both work.
//
// This is the remaining layer blocking multi-argument std::function
// construction (and the dog-food make_bvrep files), now that calling through a
// forwarding-reference callee is fixed (cpp11_forwarding_ref_callee_call).
//
// Header-free and non-vacuous (assertion 2 is a deliberately wrong claim that
// must FAIL).  Flip to CORE once forwarding-reference parameter-pack pattern
// expansion substitutes the type pack in lockstep.

extern "C" void __CPROVER_assert(int, const char *);

template <class F, class... A>
int invk(F f, A &&... a)
{
  return f(static_cast<A &&>(a)...);
}

struct C
{
  int operator()(int a, int b) const
  {
    return a * 10 + b;
  }
};

int main()
{
  C c;
  int r = invk(c, 3, 7);
  __CPROVER_assert(r == 37, "forwarding-reference pack forwards correctly");
  __CPROVER_assert(r == 0, "WRONG must FAIL");
  return 0;
}
