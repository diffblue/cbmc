extern "C" void __CPROVER_assert(bool, const char *);
template <class _Tp>
struct base
{
};
struct derived : base<derived>
{
  int n;
};
struct maker
{
  derived operator()(int __n) const
  {
    return derived{{}, __n};
  }
};
int main()
{
  maker m;
  derived d = m(7);
  __CPROVER_assert(d.n == 7, "aggregate init with template base initializer");
  return 0;
}
