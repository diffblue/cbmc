// N5008 [class.copy.elis] + [class.copy.ctor]: returning a local by
// value materializes the result via the move constructor (possibly
// elided -- but elision must behave AS IF the constructor chain ran).
// For a class whose invariant ties a pointer member to its own buffer
// (the SSO small-string shape: libstdc++ basic_string's _M_p /
// _M_local_buf), the move constructor REBASES the pointer to the
// destination's buffer when the source is self-pointing.
//
// This used to be a KNOWNBUG: the returned object was relocated
// BITWISE through the return-value mechanism, so a move constructor
// that CONDITIONALLY overwrites the rebased pointer (as every SSO move
// constructor does) left the pointer targeting the return-value
// temporary's buffer (a dead object) -- std::string returned by value
// read a dead object.  Fixed by constructing the result directly into
// caller-provided storage (elide_cpp_returned_temporaries; guaranteed
// copy elision as real ABIs implement it, Itanium: sret) with
// [class.copy.elis]/3 implicit move at the return site.
//
// g++/clang++ verify at runtime.
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
