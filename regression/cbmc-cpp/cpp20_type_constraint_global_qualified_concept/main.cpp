extern "C" void __CPROVER_assert(bool, const char *);
namespace lib
{
typedef decltype(sizeof(0)) size_t;
namespace ranges
{
template <class T>
concept small = sizeof(T) <= 4;
}
// N5008 [temp.param]/2: a type-constraint's nested-name-specifier may
// begin with `::' ([expr.prim.id.qual]/1)
template <::lib::ranges::small T>
int pick(T)
{
  return 1;
}
template <class T>
int pick(T)
{
  return 2;
}
// ... and so may the type of a non-type template parameter
template <::lib::size_t N>
int size()
{
  return N;
}
template <class T>
struct box
{
  static constexpr int n = sizeof(T);
  box(const T &)
  {
  }
};
// a deduction guide constrained like the MSVC STL's std::span guide,
// `template <::std::ranges::contiguous_range _Rng>'
template <::lib::ranges::small R>
box(R &&) -> box<R>;
} // namespace lib
int main()
{
  char c = 0;
  __CPROVER_assert(lib::pick(c) == 1, "constrained template chosen");
  __CPROVER_assert(lib::pick(0.0) == 2, "unconstrained template chosen");
  __CPROVER_assert(lib::size<3>() == 3, "non-type parameter");
  lib::box b{c};
  __CPROVER_assert(decltype(b)::n == 1, "constrained deduction guide");
  __CPROVER_assert(lib::pick(c) == 2, "WRONG (must FAIL)");
  return 0;
}
