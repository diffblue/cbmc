// N5008 [expr.cond]/7.2: when the second and third operands of the
// conditional operator are prvalues of arithmetic or (unscoped) enumeration
// type, the usual arithmetic conversions bring them to a common type.  The
// front end converted one operand to the other's type instead: `b ? c : s'
// with `char c; short s' was a short, `b ? 1.0 : 2.0f' a float.  (/4 and
// /7.1: operands of the same type keep it -- `b ? c : c' is an lvalue char,
// unlike in C.)
extern "C" void __CPROVER_assert(bool, const char *);
template <class T, class U>
struct same
{
  static const bool value = false;
};
template <class T>
struct same<T, T>
{
  static const bool value = true;
};
enum color
{
  red = 1
};
int main()
{
  char c = 1;
  short s = 2;
  unsigned u = 3;
  bool b = true;
  __CPROVER_assert(same<decltype(b ? c : s), int>::value, "char, short: int");
  __CPROVER_assert(
    same<decltype(b ? c : c), char &>::value, "same type: lvalue kept (/4)");
  __CPROVER_assert(
    same<decltype(b ? +c : +c), int>::value, "same prvalue type kept (/7.1)");
  __CPROVER_assert(
    same<decltype(b ? 1.0 : 2.0f), double>::value, "double, float: double");
  __CPROVER_assert(
    same<decltype(b ? -1 : u), unsigned>::value, "int, unsigned: unsigned");
  __CPROVER_assert(
    same<decltype(b ? red : 2L), long>::value, "enum, long: long");
  __CPROVER_assert((b ? -1 : u) == 4294967295u, "value converted to unsigned");
  __CPROVER_assert(
    (!b ? c : s) == 2 && sizeof(b ? c : s) == sizeof(int), "value and size");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
