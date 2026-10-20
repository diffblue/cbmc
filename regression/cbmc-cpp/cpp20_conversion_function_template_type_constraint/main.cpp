extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
concept integral = __is_integral(T);
struct wide
{
  unsigned long long w;
  // N5008 [temp.param]/4, [temp.constr.decl]/3, [temp.deduct]/5: the
  // type-constraint `integral' is an associated constraint of the
  // conversion function template; for a class target it is not satisfied
  // and the template is not a candidate (the MSVC STL's _Base128)
  template <integral T>
  constexpr operator T() const noexcept
  {
    return static_cast<T>(w);
  }
};
struct aggregate
{
  int v;
};
int pick(aggregate)
{
  return 1;
}
int pick(...)
{
  return 2;
}
int main()
{
  wide b{7};
  long l = b;
  __CPROVER_assert(l == 7 && pick(b) == 2, "only integral targets");
  __CPROVER_assert(pick(b) == 1, "WRONG (must FAIL)");
  return 0;
}
