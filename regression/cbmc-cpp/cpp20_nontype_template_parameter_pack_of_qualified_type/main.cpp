extern "C" void __CPROVER_assert(bool, const char *);
namespace N
{
typedef unsigned long size_type;
}
// N5008 [temp.param]/1, [temp.variadic]/1: `N::size_type... I' declares a
// non-type template parameter pack of a qualified type (`std::size_t...
// I' in user code, preprocessed with the MSVC STL)
template <N::size_type... I>
struct indices
{
  static constexpr int count = sizeof...(I);
};
template <class X, N::size_type... I>
struct tagged
{
  static constexpr int count = sizeof...(I);
};
int main()
{
  __CPROVER_assert(
    indices<0, 1>::count == 2 && tagged<int, 4, 5, 6>::count == 3 &&
      indices<>::count == 0,
    "packs of a qualified type");
  __CPROVER_assert(indices<0, 1>::count == 1, "WRONG (must FAIL)");
  return 0;
}
