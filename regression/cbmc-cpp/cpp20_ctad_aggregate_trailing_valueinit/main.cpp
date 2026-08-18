// N5008 [dcl.init.aggr]/5 (via [dcl.init.general]/16.6.2.2, C++20
// parenthesized aggregate initialization after CTAD): when the
// initializer list has FEWER entries than the aggregate has elements,
// the remaining elements are value-initialized.  `take_view(3)` with a
// two-member take_view<int> initializes __base_ from 3 and
// value-initializes __count_ to 0.  Previously the single-argument
// route was gated to single-member aggregates and this shape fell into
// the explicit-cast path ("invalid explicit cast").
extern "C" void __CPROVER_assert(bool, const char *);
template <class _From, class>
concept convertible_to = requires { _From(); };
template <class _View> struct take_view
{
  _View __base_;
  _View __count_;
};
template <class _Range, convertible_to<_Range> _Np>
auto taker(_Range, _Np __n)
{
  return take_view(__n);
}
int main()
{
  auto tv = taker(0, 3);
  __CPROVER_assert(
    tv.__base_ == 3 && tv.__count_ == 0, "aggr padding value-init");
  return 0;
}
