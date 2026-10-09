extern "C" void __CPROVER_assert(bool, const char *);
template <class _Tp>
constexpr bool is_lvalue_reference_v = false;
template <class _Tp>
constexpr bool is_lvalue_reference_v<_Tp &> = true;
namespace ranges
{
template <class _Tp>
concept viewable_range = is_lvalue_reference_v<_Tp>;
}
template <class _Closure>
struct range_adaptor
{
  // [temp.deduct.call]/3: _View&& with _View a (constrained) template
  // parameter is a forwarding reference; for the lvalue array
  // argument _View deduces to int (&)[5] ([temp.deduct.call]/2).
  template <ranges::viewable_range _View>
  friend int operator|(_View &&__view, range_adaptor)
  {
    return __view[1];
  }
};
int main()
{
  int arr[] = {1, 2, 3, 4, 5};
  range_adaptor<int> take3;
  int r = arr | take3;
  __CPROVER_assert(
    r == 2, "array lvalue binds forwarding ref of constrained friend");
  return 0;
}
