extern "C" void __CPROVER_assert(bool, const char *);
struct H
{
  int v;
  int &get()
  {
    return v;
  }
};
// [basic.lookup.qual.general]/2-3: eh in x.eh::get() is a member-qualified
// name, looked up in the type of x, C, where it names H (libstdc++'s
// _Hash_code_base::_M_swap, `__x.__ebo_hash::_M_get()')
struct C : H
{
  typedef H eh;
  int f(C &x)
  {
    return x.eh::get();
  }
  int g(C &x)
  {
    return x.eh::v;
  }
};
// [class.access.base]/6, [class.mi]/4: with A twice in the lattice, rb::i is
// the i of the R subobject's A
struct A
{
  int i;
};
struct L : A
{
};
struct R : A
{
};
struct D : L, R
{
  typedef R rb;
  int r(D &x)
  {
    return x.rb::i;
  }
};
int main()
{
  C a, b;
  b.v = 2;
  __CPROVER_assert(a.f(b) == 2, "member function");
  __CPROVER_assert(a.g(b) == 2, "data member");
  __CPROVER_assert(b.eh::v == 2, "outside a member function");
  D d;
  d.L::i = 3;
  d.R::i = 4;
  __CPROVER_assert(d.r(d) == 4, "repeated base");
  __CPROVER_assert(a.f(b) != 2, "WRONG (must FAIL)");
}
