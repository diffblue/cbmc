// N5008 [dcl.init.aggr]: designated initializers.
extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  int a, b;
};
int main()
{
  S s{.a = 1, .b = 2};
  __CPROVER_assert(s.a == 1 && s.b == 2, "designated initializers");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
