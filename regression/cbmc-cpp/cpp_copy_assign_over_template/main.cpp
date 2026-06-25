// Same-type assignment must use the (non-template) implicit copy-assignment
// operator, not a converting `operator=` function template.
//
// N5008 [class.copy.assign]/1: a copy-assignment operator is a non-template
// non-static member function `X::operator=` taking one parameter of type X,
// X&, const X&, ... ; a *template* assignment operator is never a copy
// assignment operator and does not suppress the implicitly-declared one.  For
// `b = a` with `a`, `b` of the same class, both the implicit copy assignment
// (binding the argument to `const X&` — an identity conversion,
// [over.ics.ref]) and the converting template `operator=(U)` deduced with
// `U = X` (a by-value identity match) are viable.  Their conversion sequences
// are indistinguishable, so the non-template copy assignment is preferred
// ([over.match.best]/2.4).  The top-level cv-qualification of the reference
// binding is only a tie-breaker between reference bindings
// ([over.ics.rank]/3.2.6) and must not let the by-value template match win.

extern "C" int __VERIFIER_nondet_int();
extern "C" void __CPROVER_assert(int, const char *);

struct M
{
  int v;
  M() : v(0)
  {
  }
  // Converting assignment template: would set v to 777 if (wrongly) selected
  // for a same-type assignment.
  template <typename U>
  M &operator=(U)
  {
    v = 777;
    return *this;
  }
};

int main()
{
  int x = __VERIFIER_nondet_int();
  M a;
  a.v = x;
  M b;
  b = a; // same-type: must use the implicit copy assignment (b.v == x)
  __CPROVER_assert(b.v == x, "same-type assignment uses the copy assignment");
  return 0;
}
