extern "C" void __CPROVER_assert(bool, const char *);
// long and long long have the same width here, as long and int on Windows
long load(const volatile long *p)
{
  return *p;
}
long long load(const volatile long long *p)
{
  return *p + 100;
}
struct counter
{
  long long uses;
  long get()
  {
    // N5008 [expr.reinterpret.cast]/1: the result has the type named in
    // the cast, here volatile long *, which selects load(const volatile
    // long *)
    auto &v = reinterpret_cast<volatile long long &>(uses);
    return load(reinterpret_cast<volatile long *>(&v));
  }
};
int main()
{
  counter c{5};
  __CPROVER_assert(c.get() == 5, "cast to a same-width pointer type");
  __CPROVER_assert(c.get() == 105, "WRONG (must FAIL)");
  return 0;
}
