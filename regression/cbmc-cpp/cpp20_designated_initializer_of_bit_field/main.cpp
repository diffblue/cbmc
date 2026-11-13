// N5008 [dcl.init.aggr]/4.2, [class.bit]/1: a designated initializer of a
// bit-field initializes it from the converted value.  The conversion to the
// bit-field's type yielded a value of the underlying type, and the C
// initializer code it is passed to checks the types (an invariant failure,
// hidden by a typecast in that code).
extern "C" void __CPROVER_assert(bool, const char *);
struct F
{
  unsigned short a : 1;
  unsigned short b : 1;
  unsigned short c : 3;
};
F f{.b = true, .c = 5};
int main()
{
  F g = {.a = 1, .c = 9};
  __CPROVER_assert(f.a == 0 && f.b == 1 && f.c == 5, "static object");
  __CPROVER_assert(g.a == 1 && g.b == 0 && g.c == 1, "truncated to 3 bits");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
