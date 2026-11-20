extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  int x;
  double d;
};
// [temp.deduct.type]/8: T C::* deduces T and C
template <class T, class C>
T get(const C &c, T C::*pm)
{
  return c.*pm;
}
template <class T>
struct is_mop
{
  static const bool value = false;
};
template <class T, class C>
struct is_mop<T C::*>
{
  static const bool value = true;
};
int main()
{
  S s{1, 2.5};
  auto pd = &S::d;
  decltype(&S::x) px = &S::x;
  int S::*pv{};
  __CPROVER_assert(get(s, &S::x) == 1 && get(s, pd) == 2.5, "deduced");
  __CPROVER_assert(s.*px == 1 && !pv, "auto, decltype, value-initialized");
  __CPROVER_assert(is_mop<int S::*>::value && !is_mop<int *>::value, "trait");
  __CPROVER_assert(get(s, pd) == 1, "WRONG (must FAIL)");
}
