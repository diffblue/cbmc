extern "C" void __CPROVER_assert(bool, const char *);
struct L
{
  int next;
  L(int n = 1) : next(n)
  {
  }
};
struct A : L
{
  A() : L(2)
  {
  }
};
// [class.mi]/3 (Example 2): L is both a direct and an indirect base of D
struct D : A, L
{
  // [class.base.init]/2: `L(3)' names the direct base
  D() : A(), L(3)
  {
  }
  void set()
  {
    A::next = 4; // [class.mi]/5: the L subobject of A
  }
};
// the direct L subobject follows A (Itanium C++ ABI layout); it cannot be
// named ([class.member.lookup]: `L' is ambiguous in D)
static const L &direct(const D &d)
{
  return *(reinterpret_cast<const L *>(&d) + 1);
}
int main()
{
  D d;
  __CPROVER_assert(d.A::next == 2, "A's L");
  __CPROVER_assert(direct(d).next == 3, "direct L");
  D e;
  e.set();
  __CPROVER_assert(e.A::next == 4 && direct(e).next == 3, "qualified member");
  e = d;
  __CPROVER_assert(e.A::next == 2 && direct(e).next == 3, "copy assignment");
  D f = e;
  __CPROVER_assert(f.A::next == 2 && direct(f).next == 3, "copy construction");
  __CPROVER_assert(sizeof(D) == 2 * sizeof(L), "two L subobjects");
  __CPROVER_assert(direct(d).next == 2, "WRONG (must FAIL)");
}
