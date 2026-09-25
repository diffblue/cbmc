// N5008 [expr.call]/1 and [over.call.object]: a function call whose callee is
// a reference (e.g. the result of `static_cast<F&&>(f)` / `std::forward<F>(f)`)
// is performed on the referand; for a class type the call resolves to the
// referand's `operator()`.  CBMC modelled a reference-typed callee as a pointer
// and mistook it for a function pointer ("expecting code as argument"), so the
// call silently produced a nondeterministic result.  This is the callee form
// used by `std::__invoke(std::forward<F>(fn), ...)`.
//
// Header-free and non-vacuous: assertion 2 is a deliberately wrong claim that
// must FAIL, so a regression to garbage/nondet is caught.

extern "C" void __CPROVER_assert(int, const char *);

template <class F>
int call_fwd(F &&f)
{
  return static_cast<F &&>(f)(); // call through the forwarding reference
}

struct C
{
  int operator()() const
  {
    return 99;
  }
};

int main()
{
  C c;
  int r = call_fwd(c); // F deduced to C& -> callee is a reference to c
  __CPROVER_assert(r == 99, "call through forwarding-reference callee");
  __CPROVER_assert(r == 0, "WRONG must FAIL");
  return 0;
}
