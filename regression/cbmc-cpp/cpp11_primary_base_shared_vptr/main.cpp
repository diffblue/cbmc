// Layout of dynamic classes with dynamic bases: Itanium C++ ABI 2.4 (II.1), as
// implemented by g++ and clang.  N5008 leaves the layout of a non-standard-
// layout class to the implementation ([class.mem.general]/26,
// [expr.sizeof]), so the ABI is the reference here, not the standard.
//
// - A class with a PRIMARY base (its first non-virtual dynamic base in
//   declaration order) shares that base's virtual pointer: its own virtual
//   functions get entries in the same vtable, and it adds no storage.
// - The primary base subobject is laid out at offset 0, before the other
//   bases, whatever its position in the base-specifier-list.
// - Other dynamic bases keep their own virtual pointer; a call through such a
//   base pointer adjusts `this' (thunk).
//
// Offsets are measured on an object ((char*)&o.m - (char*)&o): offsetof is
// conditionally-supported for non-standard-layout classes
// ([support.types.layout]/1) and g++ rejects it here.

extern "C" void __CPROVER_assert(bool, const char *);

struct P
{
  int p;
  P() : p(1) {}
  virtual int f() { return 10; }
  virtual int h() { return 100; }
};

// shares P's vptr: sizeof(X) == sizeof(P) + sizeof(int)
struct X : P
{
  int x;
  X() : x(2) {}
  int f() override { return 20; }
  virtual int g() { return 30; }
};

// three levels: Y's entries follow X's, which follow P's
struct Y : X
{
  int y;
  Y() : y(3) {}
  int g() override { return 40; }
  int h() override { return 400; }
  virtual int k() { return 50; }
};

struct R
{
  int r;
  R() : r(7) {}
};

// primary base P laid out first although R is declared first
struct S : R, P
{
  int s;
  S() : s(9) {}
  int f() override { return 11; }
};

struct Q
{
  int q;
  Q() : q(5) {}
  virtual int m() { return 60; }
};

// two dynamic bases: P is primary (shares the vptr), Q keeps its own
struct T : P, Q
{
  int t;
  T() : t(9) {}
  int f() override { return 12; }
  int m() override { return 61; }
  virtual int g() { return 13; }
};

int main()
{
  __CPROVER_assert(sizeof(P) == 16, "P: vptr, p");
  __CPROVER_assert(sizeof(X) == 16, "X shares P's vptr: vptr, p, x");
  __CPROVER_assert(sizeof(Y) == 24, "Y: vptr, p, x, y, padding");
  __CPROVER_assert(sizeof(S) == 24, "S: [vptr p] r s");
  __CPROVER_assert(sizeof(T) == 32, "T: [vptr p] [vptr q] t padding");

  Y o;
  __CPROVER_assert((char *)&o.p - (char *)&o == 8, "Y: p after the vptr");
  __CPROVER_assert((char *)&o.x - (char *)&o == 12, "Y: x after p");
  __CPROVER_assert((char *)&o.y - (char *)&o == 16, "Y: y after x");
  P *pp = &o;
  X *px = &o;
  __CPROVER_assert(pp->f() == 20, "P* to Y: X::f");
  __CPROVER_assert(pp->h() == 400, "P* to Y: Y::h");
  __CPROVER_assert(px->g() == 40, "X* to Y: Y::g");
  __CPROVER_assert(px->f() == 20, "X* to Y: X::f");
  __CPROVER_assert(o.k() == 50, "Y::k");

  X ox;
  P *pox = &ox;
  __CPROVER_assert(pox->f() == 20, "P* to X: X::f");
  __CPROVER_assert(pox->h() == 100, "P* to X: P::h");
  __CPROVER_assert(ox.g() == 30, "X::g");

  S os;
  __CPROVER_assert((char *)&os.p - (char *)&os == 8, "S: p after the vptr");
  __CPROVER_assert((char *)&os.r - (char *)&os == 12, "S: R after P's dsize");
  __CPROVER_assert((char *)&os.s - (char *)&os == 16, "S: s after r");
  P *ps = &os;
  R *rs = &os;
  __CPROVER_assert((char *)ps - (char *)&os == 0, "S: P subobject at 0");
  __CPROVER_assert((char *)rs - (char *)&os == 12, "S: R subobject at 12");
  __CPROVER_assert(ps->f() == 11, "P* to S: S::f");
  __CPROVER_assert(rs->r == 7 && os.p == 1 && os.s == 9, "S: member values");

  T ot;
  __CPROVER_assert((char *)&ot.p - (char *)&ot == 8, "T: p");
  __CPROVER_assert((char *)&ot.q - (char *)&ot == 24, "T: q after Q's vptr");
  __CPROVER_assert((char *)&ot.t - (char *)&ot == 28, "T: t");
  P *pt = &ot;
  Q *qt = &ot;
  __CPROVER_assert((char *)qt - (char *)&ot == 16, "T: Q subobject at 16");
  __CPROVER_assert(pt->f() == 12, "P* to T: T::f");
  __CPROVER_assert(qt->m() == 61, "Q* to T: T::m through the thunk");
  __CPROVER_assert(ot.g() == 13, "T::g");
  return 0;
}
