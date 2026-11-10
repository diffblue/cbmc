extern "C" void __CPROVER_assert(bool, const char *);
enum levelt
{
  L0 = 0,
  L1 = 1
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
  renamedt<int, level> rename_ssa(int x);
};
template <levelt level>
renamedt<int, level> statet::rename_ssa(int x)
{
  return renamedt<int, level>(x + offset * level);
}
// explicit instantiation declarations ([temp.explicit])
template renamedt<int, L0> statet::rename_ssa<L0>(int x);
template renamedt<int, L1> statet::rename_ssa<L1>(int x);
int part2();
int main()
{
  part2();
  statet s;
  s.offset = 10;
  __CPROVER_assert(
    s.rename_ssa<L0>(1).value == 1 && s.rename_ssa<L1>(1).value == 11,
    "explicitly instantiated member templates");
  return 0;
}
template <class T>
T twice(T x)
{
  return x + x;
}
template int twice<int>(int);
template long twice(long);
template <class T>
struct box
{
  T v;
  T get() const
  {
    return v;
  }
};
template struct box<int>;
namespace ns
{
struct S
{
  template <int N>
  int add(int x)
  {
    return x + N;
  }
};
template int S::add<3>(int);
} // namespace ns
int part2()
{
  __CPROVER_assert(
    twice(2) == 4 && twice(3L) == 6, "explicitly instantiated free templates");
  box<int> b{5};
  __CPROVER_assert(b.get() == 5, "explicitly instantiated class template");
  ns::S s;
  __CPROVER_assert(
    s.add<3>(1) == 4 && s.add<4>(1) == 5,
    "member template explicitly instantiated inside a namespace");
  return 0;
}
