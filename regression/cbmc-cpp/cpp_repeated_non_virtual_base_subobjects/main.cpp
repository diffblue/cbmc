extern "C" void __CPROVER_assert(bool, const char *);
struct A
{
  int i;
};
struct B : A
{
};
struct C : A
{
};
// D has two distinct A subobjects, one through B and one through C
struct D : virtual B, virtual C
{
};
int main()
{
  D d;
  B &b = d;
  C &c = d;
  b.i = 1;
  c.i = 2;
  __CPROVER_assert(d.B::i == 1 && d.C::i == 2, "separate A subobjects");
  __CPROVER_assert(&static_cast<A &>(b) != &static_cast<A &>(c), "distinct");
  __CPROVER_assert(d.B::i == 2, "WRONG (must FAIL)");
}
