// N5008 [class.copy.elis] + [class.copy.ctor]: returning a local by value
// materializes the result via the move constructor (possibly elided --
// but elision must behave AS IF the constructor chain ran).  For a class
// whose invariant ties a pointer member to its own buffer (the SSO
// small-string shape: libstdc++ basic_string's _M_p / _M_local_buf), the
// move constructor REBASES the pointer to the destination's buffer when
// the source is self-pointing.
//
// KNOWNBUG: when the move constructor BRANCHES on the source's
// self-pointer state (`o.is_local()`), the returned object's pointer ends
// up targeting the RETURN-VALUE TEMPORARY's buffer (a dead object) --
// the trace shows t.p first set to t's own buffer by the constructor,
// then clobbered to tmp_obj's buffer (a bitwise copy overwriting the
// constructed value).  Without the branch (unconditional rebase) it
// works.  This breaks every SSO-style class returned by value --
// including std::string: `std::string t = make(); t.front()` reads a
// dead object (found while building the strip_string unit proof).
//
// g++/clang++ verify at runtime.  Flip to CORE (and the strip_string
// unit proof with it) when fixed.
extern "C" void __CPROVER_assert(bool, const char *);

struct S
{
  char buf[4];
  char *p;
  bool is_local() const
  {
    return p == buf;
  }
  S() : p(buf)
  {
    buf[0] = 'a';
  }
  S(const S &o) : p(buf)
  {
    buf[0] = o.buf[0];
  }
  S(S &&o) : p(buf)
  {
    if(o.is_local())
      buf[0] = o.buf[0]; // source is self-pointing: copy the payload
    else
      p = o.p; // source held an external buffer: steal it
  }
  char front() const
  {
    return *p;
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
  __CPROVER_assert(t.front() == 'a', "front through self-pointer");
  return 0;
}
