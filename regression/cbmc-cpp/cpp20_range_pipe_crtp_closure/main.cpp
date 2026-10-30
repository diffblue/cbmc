extern "C" void __CPROVER_assert(bool, const char *);
template <class _Tp>
constexpr bool is_lvalue_reference_v = false;
template <class _Tp>
constexpr bool is_lvalue_reference_v<_Tp &> = true;
namespace ranges
{
template <class _Tp>
concept viewable_range = is_lvalue_reference_v<_Tp>;
template <class _Tp>
struct __range_adaptor_closure
{
  template <viewable_range _View, class _Closure>
  friend auto operator|(_View &&__view, _Closure &&__closure)
  {
    return __closure(__view);
  }
};
struct __take_closure : __range_adaptor_closure<__take_closure>
{
  int __n;
  template <class _Range>
  auto operator()(_Range &&__r) const
  {
    return __r[__n - 2];
  }
};
struct __take_fn
{
  __take_closure operator()(int __n) const
  {
    return __take_closure{{}, __n};
  }
};
} // namespace ranges
namespace views
{
inline constexpr ranges::__take_fn take{};
}
int main()
{
  int arr[] = {1, 2, 3, 4, 5};
  int r = arr | views::take(3);
  __CPROVER_assert(r == 2, "range pipe through CRTP closure");
  return 0;
}
