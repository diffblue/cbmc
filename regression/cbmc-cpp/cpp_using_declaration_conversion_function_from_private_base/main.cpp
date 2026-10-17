extern "C" void __CPROVER_assert(bool, const char *);
struct B
{
  int v;
  operator int() const
  {
    return v;
  }
};
// [namespace.udecl]/19: the using-declaration makes B::operator int a public
// member of A, although B is a private base
struct A : private B
{
  A()
  {
    v = 4;
  }
  using B::operator int;
};
int main()
{
  A a;
  int x = a;
  __CPROVER_assert(x == 4, "using-declared conversion");
  __CPROVER_assert(x != 4, "WRONG (must FAIL)");
}
