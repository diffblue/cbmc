extern "C" void __CPROVER_assert(bool, const char *);
int g(int a, int b);
int g(int a, int b = 2);
int g(int a = 1, int b);
int g(int a, int b)
{
  return a + b;
}
struct P
{
  int reduce(int a, int b);
  int twice(int a, int b = 3);
};
int P::reduce(int a, int b = 5)
{
  return a + b;
}
int P::twice(int a = 4, int b)
{
  return a * b;
}
int main()
{
  P p;
  __CPROVER_assert(g(5) == 7 && g() == 3, "free function");
  __CPROVER_assert(p.reduce(1) == 6, "member, definition");
  __CPROVER_assert(p.twice() == 12, "member, both");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
