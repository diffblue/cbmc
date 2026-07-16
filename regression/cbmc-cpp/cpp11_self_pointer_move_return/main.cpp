// N5008 [class.copy.elis] + [class.copy.ctor]: returning a local by
// value materializes the result via the move constructor (possibly
// elided -- but elision must behave AS IF the constructor chain ran).
// For a class whose invariant ties a pointer member to its own buffer
// (the SSO small-string shape: libstdc++ basic_string's _M_p /
// _M_local_buf), the move constructor REBASES the pointer to the
// destination's buffer when the source is self-pointing.
//
// KNOWNBUG: when the move constructor CONDITIONALLY overwrites the
// rebased pointer (branching on the source's self-pointer state, as
// every SSO move constructor does), the returned object's pointer ends
// up targeting the RETURN-VALUE TEMPORARY's buffer (a dead object):
// the trace shows t.p first set to t's own buffer by the constructor,
// then clobbered to tmp_obj's buffer by a bitwise copy.  Making the
// assignment unconditional, or removing the branch, works.  This
// breaks every SSO-style class returned by value -- including
// std::string: `std::string t = make(); t.front()` reads a dead object
// (found while building the strip_string unit proof,
// regression/unit-proofs/strip_string).
//
// g++/clang++ verify at runtime.  Flip to CORE (and the strip_string
// unit proof with it) when fixed.
extern "C" void __CPROVER_assert(bool, const char *);

struct S
{
  char buf[1];
  char *p;
  S() : p(buf)
  {
  }
  S(S &&o) : p(buf)
  {
    if(o.p != o.buf) // source held an external buffer:
      p = o.p;       // steal it; otherwise keep the rebased self-pointer
  }
};

S make()
{
  S s;
  return s;
}

int main()
{
  S t = make();
  __CPROVER_assert(t.p == t.buf, "self-pointer rebased to destination");
  return 0;
}
