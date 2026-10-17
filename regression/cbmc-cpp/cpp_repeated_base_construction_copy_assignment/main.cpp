extern "C" void __CPROVER_assert(bool, const char *);
struct A
{
  int i;
  A() : i(7)
  {
  }
  int get() const
  {
    return i;
  }
  static int count;
};
int A::count = 3;
struct B : A
{
  B()
  {
    i = 1;
  }
};
struct C : A
{
  C()
  {
    i = 2;
  }
};
struct D : B, C
{
  // [class.mi]/5: explicit qualification selects the subobject
  int sum()
  {
    return B::get() + C::get();
  }
};
int main()
{
  D d;
  D e = d; // [class.copy.ctor]/14: memberwise, each A subobject
  __CPROVER_assert(d.B::i == 1 && d.C::i == 2, "constructed separately");
  __CPROVER_assert(d.sum() == 3, "member function through each base");
  __CPROVER_assert(d.B::get() == 1 && d.C::get() == 2, "qualified calls");
  __CPROVER_assert(e.B::i == 1 && e.C::i == 2, "copied separately");
  // [class.static.data]: a static member is one entity, not ambiguous
  __CPROVER_assert(d.count == 3, "static member");
  e.C::i = 9;
  d = e;
  __CPROVER_assert(d.C::i == 9 && d.B::i == 1, "assigned separately");
  __CPROVER_assert(sizeof(D) == 2 * sizeof(A), "two A subobjects");
  __CPROVER_assert(d.B::get() == 2, "WRONG (must FAIL)");
}
