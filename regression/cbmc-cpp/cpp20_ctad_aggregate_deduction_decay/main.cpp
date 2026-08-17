// N5008 [over.match.class.deduct]/1.8 + [temp.deduct.call]/2: the C++20
// AGGREGATE DEDUCTION CANDIDATE deduces class template arguments from
// the aggregate's element types, with the by-value adjustments of
// [temp.deduct.call]/2 -- an array argument decays to a pointer.  Here
// `take_view(arr, 3)` with `int arr[1]` must deduce take_view<int*>
// (the libc++ views::take pipe shape, cvise-reduced); the positional
// fallback previously deduced take_view<int[1]> and the member of
// dependent-alias type (a non-deduced context, [temp.deduct.type]/5)
// mis-took the array argument.
extern "C" void __CPROVER_assert(bool, const char *);
namespace std
{
template <class _From, class>
concept convertible_to = requires { _From(); };
template <class> using iter_difference_t = int;
template <class _Rp> using range_difference_t = iter_difference_t<_Rp>;
template <class _View> struct take_view
{
  _View __base_;
  range_difference_t<_View> __count_;
};
} // namespace std
template <class _Range, std::convertible_to<_Range> _Np>
auto taker(_Range &&__range, _Np __n)
{
  return std::take_view(__range, __n);
}
int main()
{
  int arr[1]{7};
  auto tv = taker(arr, 3);
  __CPROVER_assert(tv.__base_[0] == 7 && tv.__count_ == 3, "agg guide decay");
  return 0;
}
