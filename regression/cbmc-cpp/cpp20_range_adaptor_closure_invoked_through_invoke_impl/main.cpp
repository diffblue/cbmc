// N5008 [range.adaptor.object]/1, [func.require]/1: `a | views::transform(f)'
// calls the range adaptor closure object, which libstdc++ 16 does through
// std::__invoke and __invoke_impl (INVOKE of the _Partial closure object,
// whose operator() is a member template).  This program is the libstdc++ 16
// <ranges> machinery for it, reduced with cvise (g++ 16 compiling and
// running each candidate) and with the compiler built-ins replaced by plain
// templates; g++ 13 and clang++ 18 compile and run it.
extern "C" void __CPROVER_assert(bool, const char *);
namespace std
{
template <int __v>
struct integral_constant
{
  static constexpr int value = __v;
};
template <bool __v>
using __bool_constant = integral_constant<__v>;
struct __conditional
{
  template <typename _Tp, typename>
  using type = _Tp;
};
template <bool, typename _If, typename _Else>
using __conditional_t = __conditional::type<_If, _Else>;
template <typename _Tp, typename _Up = _Tp>
_Up __declval(int);
template <typename _Tp>
auto declval() -> decltype(__declval<_Tp>(0));
template <typename _Tp>
struct remove_reference
{
  using type = _Tp;
};
template <typename _Tp>
struct remove_reference<_Tp &>
{
  using type = _Tp;
};
template <typename _Tp>
struct remove_reference<_Tp &&>
{
  using type = _Tp;
};
template <typename _Tp>
using remove_reference_t = remove_reference<_Tp>::type;
template <typename _Tp>
using __decay_t = _Tp;
template <typename _Tp>
struct __success_type
{
  using type = _Tp;
};
template <bool, bool, typename...>
struct __result_of_impl;
template <typename _Fn, typename... _Args>
__success_type<decltype(_Fn()(declval<_Args>()...))> _S_test(int);
template <typename _Functor, typename... _ArgTypes>
struct __result_of_impl<false, false, _Functor, _ArgTypes...>
{
  using type = decltype(_S_test<_Functor, _ArgTypes...>(0));
};
template <typename _Functor, typename... _ArgTypes>
struct __invoke_result
  : __result_of_impl<false, false, _Functor, _ArgTypes...>::type
{
};
template <typename _Tp>
constexpr bool is_array_v = false;
template <typename _Tp, decltype(sizeof(0)) _N>
constexpr bool is_array_v<_Tp[_N]> = true;
template <typename>
bool is_lvalue_reference_v;
template <typename _Tp>
constexpr bool is_lvalue_reference_v<_Tp &> = true;
template <typename _Tp, typename _Up>
constexpr bool is_same_v = false;
template <typename _Tp>
constexpr bool is_same_v<_Tp, _Tp> = true;
template <typename _Tp>
constexpr bool is_bounded_array_v = is_array_v<_Tp>;
namespace __detail
{
template <typename _Tp, typename _Up>
concept __same_as = is_same_v<_Tp, _Up>;
}
template <typename _Tp, typename _Up>
concept same_as = __detail::__same_as<_Up, _Tp>;
namespace __detail
{
template <typename _Tp, typename _Up>
concept __different_from = !same_as<_Tp, _Up>;
}
template <typename _From, typename>
concept convertible_to = requires
{
  _From();
};
template <typename _Tp>
concept move_constructible = convertible_to<_Tp, _Tp>;
template <typename _Tp>
concept copy_constructible = move_constructible<_Tp>;
template <typename>
void forward()
{
}
template <typename _Iter>
concept input_or_output_iterator = requires(_Iter __i)
{
  __i;
};
template <typename _Iter>
concept input_iterator = input_or_output_iterator<_Iter>;
namespace ranges::__access
{
template <typename _Tp>
concept __member_begin = requires(_Tp __t)
{
  __decay_t<decltype(__t.begin())>();
  __decay_t<decltype(0)>();
};
template <typename _Tp>
auto __begin(_Tp &__t)
{
  if constexpr(is_array_v<_Tp>)
    return __t;
  if constexpr(__member_begin<_Tp>)
    return __t.begin();
}
} // namespace ranges::__access
namespace __detail
{
template <typename _Tp>
using __range_iter_t = decltype(ranges::__access::__begin(declval<_Tp &>()));
}
namespace ranges
{
inline namespace __detail
{
template <typename _Tp>
concept __maybe_borrowed_range = is_lvalue_reference_v<_Tp>;
}
namespace __access
{
struct _Begin
{
  template <__maybe_borrowed_range _Tp>
  auto operator()(_Tp &&__t)
  {
    return __t.begin();
  }
};
template <typename _Tp>
concept __member_end = requires(_Tp __t)
{
  __decay_t<decltype(__t.end())>();
  __decay_t<decltype(0)>();
};
struct _End
{
  template <__maybe_borrowed_range _Tp>
  auto operator()(_Tp &&__t)
  {
    if constexpr(is_bounded_array_v<remove_reference_t<_Tp>>)
      return __t;
    if constexpr(__member_end<_Tp>)
      return __t.end();
  }
};
} // namespace __access
namespace
{
__access::_Begin begin;
__access::_End end;
} // namespace
template <typename>
concept range = requires
{
  end;
};
template <typename _Tp>
using iterator_t = std::__detail::__range_iter_t<_Tp>;
template <range _Range>
using sentinel_t = decltype(end(declval<_Range &>()));
namespace
{
template <typename>
void __is_derived_from_view_interface_fn();
template <typename>
concept __is_derived_from_view_interface = requires
{
  __is_derived_from_view_interface_fn;
};
} // namespace
template <typename _Tp>
constexpr bool enable_view = __is_derived_from_view_interface<_Tp>;
template <typename _Tp>
concept view = enable_view<_Tp>;
template <typename _Tp>
concept input_range = input_iterator<_Tp>;
template <typename _Tp>
concept viewable_range = (!view<_Tp>);
} // namespace ranges
template <typename _Res, typename _Fn, typename... _Args>
_Res __invoke_impl(_Fn __f, _Args &&...__args)
{
  return __f(__args...);
}
template <typename _Callable, typename... _Args>
__invoke_result<_Callable, _Args...>::type
__invoke(_Callable __fn, _Args &&...__args)
{
  return __invoke_impl<typename __invoke_result<_Callable, _Args...>::type>(
    __fn, __args...);
}
namespace ranges
{
namespace
{
using std::__detail::__different_from;
}
} // namespace ranges
template <int, typename _Fd, typename...>
struct _Binder
{
  template <typename _Fn>
  _Binder(_Fn)
  {
  }
  template <typename _Tp, typename... _CallArgs>
  static auto _S_call(_Tp, _CallArgs &&...__call_args)
  {
    _Tp __trans_tmp_1 = forward<_Tp>;
    _Tp __trans_tmp_2 = forward<_Tp>;
    return __invoke(
      __trans_tmp_1._M_fd, __call_args..., __trans_tmp_2._M_bound_args);
  }
  _Fd _M_fd;
  decltype(0) _M_bound_args;
};
template <typename _Fn, typename... _Args>
using _Bind_back_t = _Binder<0, _Fn, _Args...>;
namespace ranges
{
namespace
{
struct _ViaPointer
{
  auto _M_call_deref()
  {
    return 0;
  }
};
template <typename>
auto __select()
{
  return _ViaPointer();
}
template <typename, typename... _Iters>
using __func_handle_t = decltype(__select<_Iters...>());
template <bool _Const, typename _Tp>
using __maybe_const_t = __conditional_t<_Const, _Tp, _Tp>;
;
}; // namespace
template <typename, typename... _Args>
concept __adaptor_partial_app_viable = sizeof...(_Args) == 1;
template <typename...>
struct _Partial;
template <typename _Self, typename _Range>
auto operator|(_Range &&__r, _Self __self)
{
  return __self(__r);
}
template <typename _Derived>
struct _RangeAdaptor
{
  template <typename... _Args>
  requires __adaptor_partial_app_viable<_Derived, _Args...> auto
  operator()(_Args...)
  {
    return _Partial<_Derived, _Args...>{0, forward<_Args>...};
  }
};
template <typename _Adaptor, typename... _Args>
struct _Partial<_Adaptor, _Args...>
{
  using _Binder = _Bind_back_t<_Adaptor, _Args...>;
  _Binder _M_binder;
  template <typename... _Ts>
  _Partial(int, _Ts...) : _M_binder(forward<_Ts>...)
  {
  }
  template <typename _Range>
  auto operator()(_Range &&__r)
  {
    return _Binder::_S_call(_M_binder, __r);
  }
};
template <range _Range>
struct ref_view
{
  _Range *_M_r;
  template <__different_from<ref_view> _Tp>
  ref_view(_Tp)
  {
  }
  iterator_t<_Range> begin()
  {
    return *_M_r;
  }
  sentinel_t<_Range> end()
  {
    return *_M_r;
  }
};
template <typename _Range>
ref_view(_Range &) -> ref_view<_Range>;
namespace views
{
namespace __detail
{
template <typename _Range>
concept __can_ref_view = requires
{
  declval<_Range>;
};
} // namespace __detail
struct
{
  template <viewable_range _Range>
  auto operator()(_Range &&__r)
  {
    return ref_view{__r};
  }
} all;
template <viewable_range _Range>
using all_t = decltype(all(declval<_Range>()));
} // namespace views
template <input_range _Vp, copy_constructible _Fp>
struct transform_view
{
  template <bool _Const>
  using _Base = __maybe_const_t<_Const, _Vp>;
  template <int _Const>
  struct _Iterator
  {
    using _Base = _Base<_Const>;
    using _Base_iter = iterator_t<_Base>;
    using _Func_handle =
      __func_handle_t<__maybe_const_t<_Const, _Fp>, _Base_iter>;
    _Base_iter _M_current;
    _Func_handle _M_fun;
    _Iterator(__maybe_const_t<_Const, transform_view> *, _Base_iter)
    {
    }
    auto operator*()
    {
      return _M_fun._M_call_deref();
    }
    void operator++()
    {
    }
    friend bool operator==(_Iterator, _Iterator __y)
    {
      return __y._M_current;
    }
  };
  _Vp _M_base;

  transform_view(_Vp, _Fp __fun) : _M_base(__fun)
  {
  }
  _Iterator<false> begin()
  {
    return {this, ranges::begin(_M_base)};
  }
  _Iterator<false> end()
  {
    return {this, ranges::end(_M_base)};
  }
};
template <typename _Range, typename _Fp>
transform_view(_Range &&, _Fp) -> transform_view<views::all_t<_Range>, _Fp>;
namespace views
{
struct _Transform : _RangeAdaptor<_Transform>
{
  template <viewable_range _Range, typename _Fp>
  auto operator()(_Range &&__r, _Fp __f)
  {
    return transform_view(__r, __f);
  }
  using _RangeAdaptor::operator();
} transform;
} // namespace views
} // namespace ranges
namespace views = ranges::views;
} // namespace std
// The reduced range types are not usable at run time (the views keep no
// range), so the range-for is only instantiated, never executed.
void transform_loop()
{
  int a[1] = {5};
  for(int x : a | std::views::transform([] {}))
    (void)x;
}

int main()
{
  int reached = 1;
  __CPROVER_assert(reached == 1, "converted");
  __CPROVER_assert(reached == 2, "WRONG (must FAIL)");
  return 0;
}
