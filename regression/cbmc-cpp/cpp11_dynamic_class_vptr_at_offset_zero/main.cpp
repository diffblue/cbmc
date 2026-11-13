// Itanium C++ ABI 2.4 II.1: a dynamic class without a primary base has its
// virtual pointer at offset 0, before every base subobject and data member,
// wherever the first virtual function is declared.  CBMC appended the
// pointer where that declaration was met (`struct A { int a; virtual int
// f(); }' had `a' at 0, sizeof still 16), and the derived-to-base
// conversion assumed the first base at offset 0.
extern "C" void __CPROVER_assert(bool, const char *);
struct A1
{
  int a;
  virtual int f()
  {
    return 1;
  }
};
struct A2
{
  char c;
  short s;
  virtual int f()
  {
    return 1;
  }
  int i;
};
struct R
{
  int r;
  R() : r(7)
  {
  }
};
struct D : R
{
  int d;
  D() : d(2)
  {
  }
  virtual int g()
  {
    return 20;
  }
};
struct E : D
{
  int e;
  E() : e(3)
  {
  }
  int g() override
  {
    return 21;
  }
};
int main()
{
  __CPROVER_assert(sizeof(A1) == 16 && alignof(A1) == 8, "A1: vptr + int");
  {
    A1 o;
    __CPROVER_assert((char *)&o.a - (char *)&o == 8, "A1.a after the vptr");
  }
  __CPROVER_assert(sizeof(A2) == 16, "A2: vptr, c, s, i");
  {
    A2 o;
    __CPROVER_assert(
      (char *)&o.c - (char *)&o == 8 && (char *)&o.s - (char *)&o == 10 &&
        (char *)&o.i - (char *)&o == 12,
      "A2 members after the vptr, whatever the position of the virtual "
      "function");
  }
  __CPROVER_assert(sizeof(D) == 16, "D: vptr, base R, d");
  {
    D o;
    __CPROVER_assert(
      (char *)&o.r - (char *)&o == 8 && (char *)&o.d - (char *)&o == 12,
      "D: the non-dynamic base R is at 8, after the vptr");
  }
  D d;
  E e;
  D *pd = &e;
  __CPROVER_assert(d.g() == 20 && pd->g() == 21, "virtual dispatch");
  __CPROVER_assert(
    pd->r == 7 && pd->d == 2 && e.e == 3,
    "base constructor ran at the base's offset");
  return 0;
}
