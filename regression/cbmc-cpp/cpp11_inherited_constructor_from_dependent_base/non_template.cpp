extern "C" void __CPROVER_assert(bool, const char *);
struct traits
{
  int k;
};
struct tb
{
  explicit tb(const traits &t) : k(t.k)
  {
  }
  int k;
};
struct tr : tb
{
  using tb::tb;
};
int main()
{
  traits t{7};
  tr x(t);
  __CPROVER_assert(x.k == 7, "inherited");
  __CPROVER_assert(x.k == 8, "WRONG (must FAIL)");
}
