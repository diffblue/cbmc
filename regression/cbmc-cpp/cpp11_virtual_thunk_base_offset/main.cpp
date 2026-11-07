// A virtual call through a pointer to a non-primary dynamic base enters the
// overrider through a thunk that adjusts `this' by the base subobject's
// offset (Itanium C++ ABI 2.5.3).  That offset includes the alignment padding
// between base subobjects: P's non-virtual part (vptr + int) is 12 bytes, Q
// is 8-aligned, so Q is at 16, not 12.  The thunk used the unpadded offset,
// so T::m read t and q from the wrong addresses.  Flattening T into U (three
// levels) also kept P's tail padding next to T's own alignment padding and
// lost Q's base-alignment mark, so U's Q subobject sat at a misaligned 20.

extern "C" void __CPROVER_assert(bool, const char *);

struct P
{
  int p;
  P() : p(1)
  {
  }
  virtual int f()
  {
    return 10;
  }
};

struct Q
{
  int q;
  Q() : q(5)
  {
  }
  virtual int m()
  {
    return 60;
  }
};

struct T : P, Q
{
  int t;
  T() : t(9)
  {
  }
  int m() override
  {
    return t * 10 + q;
  }
};

struct U : T
{
  int u;
  U() : u(3)
  {
  }
  int m() override
  {
    return t * 100 + q * 10 + u;
  }
};

int main()
{
  T ot;
  Q *qt = &ot;
  __CPROVER_assert((char *)qt - (char *)&ot == 16, "Q subobject after padding");
  __CPROVER_assert(qt->m() == 95, "T::m sees T's members through the thunk");
  U ou;
  // an indirect base's tail padding is dropped like a direct base's, and the
  // base-alignment mark of Q's subobject survives the second flattening
  __CPROVER_assert(
    (char *)&ou.q - (char *)&ou == 24, "U: q after Q's vptr at 16");
  __CPROVER_assert((char *)&ou.t - (char *)&ou == 28, "U: t after q");
  __CPROVER_assert((char *)&ou.u - (char *)&ou == 32, "U: u after t");
  __CPROVER_assert(sizeof(U) == 40, "sizeof U");
  Q *qu = &ou;
  __CPROVER_assert(qu->m() == 953, "U::m sees U's members through the thunk");
  T *tu = &ou;
  __CPROVER_assert(tu->m() == 953, "U::m through T* (shared vptr)");
  return 0;
}
