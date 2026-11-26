extern "C" void __CPROVER_assert(bool, const char *);
template <int V>
struct integral_constant
{
  using value_type = int;
  constexpr operator value_type() const
  {
    return V;
  }
};
// [temp.pre]/1, [basic.pre]/7: v<E> names an object of class type, whose
// conversion function is called; [temp.arg.nontype]/2: E (int)
// is converted to the long parameter N
template <long N>
constexpr integral_constant<N> v{};
struct span
{
  template <int E>
  span(int (&)[E]) : extent(v<E>)
  {
  }
  int extent;
};
int main()
{
  int a[3];
  span s(a);
  __CPROVER_assert(s.extent == 3, "extent from the variable template");
  __CPROVER_assert(s.extent == 0, "WRONG (must FAIL)");
}
