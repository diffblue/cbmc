// N5008 [dcl.spec.auto.general]/2, [dcl.type.auto.deduct]/4: a placeholder
// return type under a ptr-operator (`auto &`, `auto *`, `const auto &`) is
// deduced like the corresponding variable declaration, keeping the referred
// type's qualifiers.
extern "C" void __CPROVER_assert(bool, const char *);
const int ci = 3;
int mi = 4;
volatile int vi = 5;
struct S
{
  int m = 6;
  const int cm = 7;
  auto &get()
  {
    return m;
  }
  auto &cget() const
  {
    return m;
  }
  auto *pget()
  {
    return &m;
  }
  auto &cmget()
  {
    return cm;
  }
};
auto &href()
{
  return ci;
}
const auto &cref()
{
  return mi;
}
auto &vref()
{
  return vi;
}
auto *cptr()
{
  return &ci;
}
auto **pp()
{
  static int *p = &mi;
  return &p;
}
// the return expression names a body-local: deduced only once the body is
// type-checked
auto **ppl()
{
  static int *p = &mi;
  int **q = &p;
  return q;
}
auto &locref()
{
  int &r = mi;
  return r;
}
int main()
{
  const auto &r1 = ci;
  const auto x = ci;
  auto &r2 = mi;
  auto *p = &ci;
  static_assert(__is_same(decltype(r1), const int &), "const auto& of const");
  static_assert(__is_same(decltype(x), const int), "const auto");
  static_assert(__is_same(decltype(r2), int &), "auto& mutable");
  static_assert(__is_same(decltype(p), const int *), "auto* of const");
  static_assert(__is_same(decltype(href()), const int &), "auto& fn const");
  static_assert(__is_same(decltype(cref()), const int &), "const auto& fn");
  static_assert(
    __is_same(decltype(vref()), volatile int &), "auto& fn volatile");
  static_assert(__is_same(decltype(cptr()), const int *), "auto* fn const");
  static_assert(__is_same(decltype(pp()), int **), "auto** fn");
  static_assert(__is_same(decltype(ppl()), int **), "auto** fn, body-local");
  static_assert(__is_same(decltype(locref()), int &), "auto& fn, body-local");
  S s;
  const S cs;
  static_assert(__is_same(decltype(s.get()), int &), "member auto&");
  static_assert(
    __is_same(decltype(cs.cget()), const int &), "member auto& const this");
  static_assert(__is_same(decltype(s.pget()), int *), "member auto*");
  static_assert(
    __is_same(decltype(s.cmget()), const int &), "member auto& const member");
  s.get() = 8;
  int arr[] = {1, 2, 3};
  int sum = 0;
  for(const auto &e : arr)
    sum += e;
  __CPROVER_assert(
    s.m == 8 && *s.pget() == 8 && cs.cget() == 6 && href() == 3 &&
      **pp() == 4 && **ppl() == 4 && locref() == 4 && sum == 6,
    "values");
  __CPROVER_assert(*cptr() == 4, "WRONG (must FAIL)");
  return 0;
}
