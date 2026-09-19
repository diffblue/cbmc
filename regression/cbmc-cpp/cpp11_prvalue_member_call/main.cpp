// N5008 [expr.type.conv]/2 + [class.temporary]/2: `T()' for a class type is a
// prvalue; accessing a member materialises a temporary.  For a class without
// user-declared constructors the value-initialised prvalue was a bare struct
// constant with no object to bind the implicit object parameter to:
// `B().g()' reported "found no match for symbol 'g'".
extern "C" void __CPROVER_assert(bool, const char *);
struct B1
{
  int k;
  int g() const
  {
    return 1;
  }
  int h()
  {
    return 2;
  }
};
struct B2
{
  int k;
  B2() : k(3)
  {
  }
  int g() const
  {
    return k;
  }
};
union U
{
  int i;
  char c;
  int get() const
  {
    return i;
  }
};
int main()
{
  __CPROVER_assert(B1().g() == 1, "T(): const member function");
  __CPROVER_assert(B1().h() == 2, "T(): non-const member function");
  __CPROVER_assert(B1().k == 0, "T() value-initialises ([dcl.init.general]/9)");
  __CPROVER_assert(B2().g() == 3, "T() with a user-declared constructor");
  __CPROVER_assert(B1{}.g() == 1, "T{}");
  __CPROVER_assert(U().get() == 0, "union");
  return 0;
}
