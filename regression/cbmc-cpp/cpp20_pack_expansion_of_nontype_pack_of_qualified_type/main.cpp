extern "C" void __CPROVER_assert(bool, const char *);
namespace N
{
typedef unsigned long size_type;
}
template <N::size_type... I>
struct indices
{
};
// N5008 [temp.param]/1, [temp.variadic]/5: `I...' in `indices<I...>' is a
// pack expansion of the non-type parameter pack I (the shape of user code
// with `std::size_t... I' and an index_sequence)
template <N::size_type... I>
constexpr int count(indices<I...>)
{
  return sizeof...(I);
}
struct holder
{
  template <N::size_type... I>
  int call(indices<I...>) const
  {
    return sizeof...(I);
  }
};
int main()
{
  holder h;
  __CPROVER_assert(
    count(indices<1, 2>{}) == 2 && h.call(indices<0, 1, 2>{}) == 3,
    "deduced from indices<I...>");
  __CPROVER_assert(count(indices<1, 2>{}) == 1, "WRONG (must FAIL)");
  return 0;
}
