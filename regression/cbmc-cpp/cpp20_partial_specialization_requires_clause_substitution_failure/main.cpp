// N5008 [temp.constr.atomic]/3, [temp.spec.partial.match]/2: a partial
// specialization whose requires-clause `T::is_special' is ill-formed after
// substitution (T = int *) is not satisfied, so it does not match.  CBMC
// used to leave a clause it could not type-check open and treat it as
// satisfied.  libc++ constrains its join_view specialization of
// __segmented_iterator_traits this way: with <ranges> included, int * was
// taken for a segmented iterator, and std::ranges::find on an array called
// __find_segment_if (cpp20_libcxx_header_drops/test_ranges_find).
extern "C" void __CPROVER_assert(bool, const char *);
template <bool B>
struct bc
{
  static constexpr bool value = B;
};
template <class T>
struct traits;
template <class T>
requires(T::is_special) struct traits<T>
{
  static constexpr int kind = 1;
};
template <class T, decltype(sizeof(int)) = 0>
struct has_spec : bc<false>
{
};
template <class T>
struct has_spec<T, sizeof(T) * 0> : bc<true>
{
};
struct special
{
  static constexpr bool is_special = true;
};
struct plain
{
  static constexpr bool is_special = false;
};
int main()
{
  __CPROVER_assert(has_spec<traits<special>>::value, "constraint satisfied");
  __CPROVER_assert(!has_spec<traits<plain>>::value, "constraint false");
  __CPROVER_assert(!has_spec<traits<int *>>::value, "substitution failure");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
