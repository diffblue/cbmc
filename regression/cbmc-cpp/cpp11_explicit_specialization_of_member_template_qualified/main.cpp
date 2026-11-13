extern "C" void __CPROVER_assert(bool, const char *);
namespace ns
{
struct statet
{
  int offset;
  template <int level>
  int set_indices(int x);
  template <class T>
  T conv(int x);
};
template <>
int statet::set_indices<0>(int x)
{
  return x;
}
template <>
int statet::set_indices<1>(int x)
{
  return x + offset;
}
template <>
long statet::conv<long>(int x)
{
  return x * 2L;
}
template <class T>
T free_conv(int x)
{
  return T(x);
}
template <>
long free_conv<long>(int x)
{
  return x * 3L;
}
} // namespace ns
template <>
short ns::statet::conv<short>(int x)
{
  return static_cast<short>(x * 4);
}
int part2()
{
  ns::statet s;
  s.offset = 10;
  __CPROVER_assert(
    s.set_indices<0>(1) == 1 && s.set_indices<1>(1) == 11,
    "member NTTP specializations in a namespace");
  __CPROVER_assert(
    s.conv<long>(2) == 4 && s.conv<short>(2) == 8,
    "member type-parameter specializations, one declared outside the "
    "namespace");
  __CPROVER_assert(
    ns::free_conv<long>(2) == 6 && ns::free_conv<int>(2) == 2,
    "free function specialization untouched");
  return 0;
}
enum levelt
{
  L0 = 0,
  L1 = 1,
  L2 = 2
};
template <class T, levelt L>
struct renamedt
{
  T value;
  explicit renamedt(T v) : value(v)
  {
  }
};
struct statet
{
  int offset;
  template <levelt level>
  renamedt<int, level> set_indices(int x);
};
template <>
renamedt<int, L0> statet::set_indices<L0>(int x)
{
  return renamedt<int, L0>(x);
}
template <>
renamedt<int, L1> statet::set_indices<L1>(int x)
{
  return renamedt<int, L1>(x + offset);
}
template <>
renamedt<int, L2> statet::set_indices<L2>(int x)
{
  return renamedt<int, L2>(x + 2 * offset);
}
int part2();
int main()
{
  part2();
  statet s;
  s.offset = 10;
  __CPROVER_assert(s.set_indices<L0>(1).value == 1, "L0 specialization");
  __CPROVER_assert(s.set_indices<L1>(1).value == 11, "L1 specialization");
  __CPROVER_assert(s.set_indices<L2>(1).value == 21, "L2 specialization");
  return 0;
}
