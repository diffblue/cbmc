// N5008 [expr.sub]/1: E1[E2] is an lvalue if E1 is an lvalue and an xvalue
// otherwise; [class.temporary]/6.3 (Example 2): `int &&a = id<int[3]>{1,
// 2, 3}[i]' binds the rvalue reference to the xvalue and the temporary
// array has the lifetime of a.  The subscript was taken for a genuine
// lvalue ([dcl.init.ref]/5.4) and the binding rejected ("bad reference
// initializer").
extern "C" void __CPROVER_assert(bool, const char *);
using arr3 = int[3];
struct P
{
  int a[3];
};
int main()
{
  int i = 1;
  int &&d = arr3{1, 2, 3}[i];
  const int &e = arr3{4, 5, 6}[2];
  const int &f = P{{7, 8, 9}}.a[i];
  __CPROVER_assert(d == 2, "6.3 subscript of array prvalue");
  __CPROVER_assert(e == 6, "const subscript");
  __CPROVER_assert(f == 8, "6.4 member then subscript");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
