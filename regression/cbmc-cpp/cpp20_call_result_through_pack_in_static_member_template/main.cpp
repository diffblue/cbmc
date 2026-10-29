// N5008 [over.match.best]/2.5, [over.ics.rank]/2.1, [temp.deduct.partial]:
// in `_Fn()(declval<_Args>...)' with _Fn = _Transform, the constrained
// two-parameter operator() template is viable (viewable_range holds: the
// substitution in view's sentinel_t fails, [temp.constr.atomic]/3) and is
// better than the C-style variadic operator() brought in by the
// using-declaration (an ellipsis conversion sequence is the worst), also
// when _S_test's template arguments come from the pack of __invoke, called
// from _Binder::_S_call.  Reduced with cvise (g++ 13 and clang++ 18 checking
// each candidate, the assertion as a static_assert) from
// cpp20_range_adaptor_closure_invoked_through_invoke_impl; declval<_Args>...
// passes the functions themselves, as cvise left it.
extern "C" void __CPROVER_assert(bool, const char *);
template <typename>
void __declval(int);
template <typename _Tp>
auto declval() -> decltype(__declval<_Tp>(0));
template <typename _Tp>
struct __success_type
{
  using type = _Tp;
};
template <typename _Fn, typename... _Args>
__success_type<decltype(_Fn()(declval<_Args>...))> _S_test(int);
template <typename>
struct __invoke_result;
template <typename, typename>
bool is_same_v;
namespace __detail
{
template <typename _Tp, typename _Up>
concept __same_as = is_same_v<_Tp, _Up>;
}
template <typename _Tp, typename _Up>
concept same_as = __detail::__same_as<_Up, _Tp>;
template <typename>
void forward();
int end;
template <typename>
concept range = requires
{
  end;
};
template <range _Range>
using sentinel_t = decltype(end(declval<_Range>()));
template <typename _Tp>
concept view = same_as<_Tp, sentinel_t<_Tp>>;
template <typename _Tp>
concept viewable_range = !view<_Tp>;
template <typename...>
struct _Partial;
template <class>
struct is_partial_p
{
  static constexpr bool value = false;
};
template <class... A>
struct is_partial_p<_Partial<A...>>
{
  static constexpr bool value = true;
};
template <typename _Callable, typename... _Args>
void __invoke(_Callable, _Args...)
{
  __CPROVER_assert(
    !is_partial_p<typename decltype(_S_test<_Callable, _Args...>(
      0))::type>::value,
    "two-parameter operator() selected");
}
template <typename _Fd>
struct _Binder
{
  template <typename _Tp, typename... _CallArgs>
  static void _S_call(_Tp, _CallArgs... __call_args)
  {
    __invoke(_Fd(), __call_args..., 0);
  }
};
struct _RangeAdaptor
{
  template <typename... _Args>
  auto operator()(...)
  {
    return _Partial{0, forward<_Args>...};
  }
};
template <typename _Adaptor, typename... _Args>
struct _Partial<_Adaptor, _Args...>
{
};
struct _Transform : _RangeAdaptor
{
  template <viewable_range _Range, typename _Fp>
  void operator()(_Range, _Fp);
  using _RangeAdaptor::operator();
} main_a;
void b()
{
}
int main()
{
  _Binder<_Transform>::_S_call(b, main_a);
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
