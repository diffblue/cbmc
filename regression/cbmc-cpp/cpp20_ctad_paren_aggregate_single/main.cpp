// N5008 [over.match.class.deduct] + [dcl.init.general]/16.6.2.2: CTAD
// on an aggregate class template with a SINGLE parenthesized argument
// (`std::take_view(__n)` inside a function template, the cvise-reduced
// libc++ views::take shape).  Deduction picks take_view<int>; with no
// viable constructor and take_view an aggregate, the argument
// initializes the single member (C++20 parenthesized aggregate
// initialization).  Previously the deduced single-argument call fell
// into the explicit-cast path and died with "invalid explicit cast:
// operand type: 'signed int' casting to: 'struct take_view'".
extern "C" void __CPROVER_assert(bool, const char *);
namespace std
{
template <class _From, class>
concept convertible_to = requires { _From(); };
template <class _View> struct take_view
{
  _View range_difference_t;
};
} // namespace std
template <class _Range, std::convertible_to<_Range> _Np>
auto taker(_Range, _Np __n)
{
  return std::take_view(__n);
}
int main()
{
  auto tv = taker(0, 3);
  __CPROVER_assert(tv.range_difference_t == 3, "ctad in template");
  return 0;
}
