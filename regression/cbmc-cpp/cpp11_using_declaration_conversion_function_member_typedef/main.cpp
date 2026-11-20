extern "C" void __CPROVER_assert(bool, const char *);
struct B
{
  int v;
  operator int() const
  {
    return v;
  }
};
// [basic.lookup.unqual]/5: I in the conversion-type-id is looked up in B
// first and, finding nothing there, by unqualified lookup from the
// using-declaration, which finds A::I (libstdc++'s atomic<int>, `using
// __base_type::operator __integral_type;')
struct A : B
{
  typedef int I;
  using B::operator I;
};
int main()
{
  A a;
  a.v = 1;
  int x = a;
  __CPROVER_assert(x == 1, "inherited conversion");
  __CPROVER_assert(x != 1, "WRONG (must FAIL)");
}
