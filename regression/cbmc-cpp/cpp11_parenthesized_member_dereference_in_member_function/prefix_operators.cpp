extern "C" void __CPROVER_assert(bool, const char *);
typedef int T;
struct s
{
  int x = 5;
  int *p;
  s() : p(&x)
  {
  }
  bool b = true;
  int run()
  {
    int r = 0;
    r += (-(x)-1 == -6);  // (-x) - 1
    r += (*(p)*2 == 10);  // (*p) * 2
    r += ((!(b)&1) == 0); // (!b) & 1
    r += (-(T)-1 == 1);   // -(T)(-1): a cast
    r += (*(p) + 1 == 6); // (*p) + 1
    r += (~(x)&7) == 2;   // (~x) & 7
    return r;
  }
};
int main()
{
  s v;
  __CPROVER_assert(
    v.run() == 6, "prefix operator binds to the parenthesized name");
  __CPROVER_assert(v.run() == 5, "WRONG (must FAIL)");
}
