extern "C" void __CPROVER_assert(bool, const char *);
struct A
{
  int i;
};
struct B : A
{
  int j;
};
struct C : A
{
  int k;
};
// N5008 [class.mi]/4-5: D has two A subobjects, one in B and one in C
struct D : B, C
{
  int l;
  void set()
  {
    B::i = 1;
    C::i = 2;
  }
};
int main()
{
  D d;
  d.set();
  B &b = d;
  C &c = d;
  __CPROVER_assert(d.B::i == 1 && d.C::i == 2, "qualified access");
  __CPROVER_assert(b.i == 1 && c.i == 2, "through the bases");
  __CPROVER_assert(
    &static_cast<A &>(b) != &static_cast<A &>(c), "distinct subobjects");
  c.i = 5;
  __CPROVER_assert(d.B::i == 1 && d.C::i == 5, "writes stay apart");
  __CPROVER_assert(d.B::i == 5, "WRONG (must FAIL)");
}
