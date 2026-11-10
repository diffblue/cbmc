extern "C" void __CPROVER_assert(bool, const char *);
typedef decltype(sizeof(0)) size_t;
template <class T, T... I>
struct iseq
{
};
template <size_t... I>
using seq = iseq<size_t, I...>;
template <size_t I>
int get(const int *a)
{
  return a[I];
}
// N5008 [temp.deduct.call]/1: for a braced-init-list argument the
// parameter `seq<I...>' is a non-deduced context; [temp.arg.explicit]/4:
// the trailing pack I is then deduced as an empty sequence
template <int... I>
int count(int, iseq<int, I...>)
{
  return sizeof...(I);
}
const int va[] = {5}, vb[] = {7};
struct pr
{
  int first = 9;
  int second = 9;
  // the MSVC STL pair's delegation to its piecewise constructor
  pr() : pr(va, vb, seq<0>{}, {})
  {
  }
  template <class A, class B, size_t... I1, size_t... I2>
  pr(A a, B b, seq<I1...>, seq<I2...>)
    : first(get<I1>(a)...), second(get<I2>(b)...)
  {
  }
};
int main()
{
  pr p;
  __CPROVER_assert(count(1, {}) == 0, "empty pack");
  __CPROVER_assert(p.first == 5, "first");
  __CPROVER_assert(p.second == 0, "second value-initialized");
  __CPROVER_assert(p.second == 9, "WRONG (must FAIL)");
  return 0;
}
