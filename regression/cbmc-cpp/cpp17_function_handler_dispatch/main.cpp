// Header-free mimic of libstdc++ std::function dispatch (cvise-reduced
// from cpp17_std_function_lambda_call).  The lambda is stored via the
// _Function_handler pattern and invoked through the _M_invoker function
// pointer; the invocation never reaches the closure body, so the
// by-reference increment is lost.  g++/clang++ accept and run clean.
extern "C" void __CPROVER_assert(bool, const char *);

template <int __v> struct integral_constant {
  static constexpr int value = __v;
};
template <bool, bool, typename...> struct __result_of_impl;
template <typename _Functor, typename... _ArgTypes>
struct __result_of_impl<false, false, _Functor, _ArgTypes...> {
  typedef decltype(0) type;
};
template <typename... _ArgTypes>
struct __invoke_result
    : __result_of_impl<integral_constant<false>::value,
                       integral_constant<false>::value, _ArgTypes...> {};
template <typename, typename _Fn, typename... _Args>
void __invoke_impl(_Fn __f, _Args &&...__args) {
  __f(__args...);
}
template <typename, typename _Callable, typename... _Args>
void __invoke_r(_Callable __fn, _Args &&...__args) {
  __invoke_impl<typename __invoke_result<_Args...>::type>(__fn, __args...);
}
template <typename> class function;
int _M_functor;
template <typename _Functor> struct _Base_manager {
  static _Functor *_M_get_pointer(int) { return 0; }
};
template <typename, typename> class _Function_handler;
template <typename _Res, typename _Functor, typename... _ArgTypes>
struct _Function_handler<_Res(_ArgTypes...), _Functor> {
  static void _M_invoke(const int &__functor, _ArgTypes... __args) {
    auto __trans_tmp_1 = _Base_manager<_Functor>::_M_get_pointer(__functor);
    __invoke_r<_Res>(*__trans_tmp_1, __args...);
  }
};
template <typename _Res, typename... _ArgTypes>
struct function<_Res(_ArgTypes...)> {
  template <typename _Functor>
  using _Handler = _Function_handler<_Res(_ArgTypes...), _Functor>;
  template <typename _Functor> function(_Functor) {
    _M_invoker = _Handler<_Functor>::_M_invoke;
  }
  void operator()(_ArgTypes... __args) {
    _M_invoker(_M_functor, _ArgTypes(__args)...);
  }
  using _Invoker_type = _Res (*)(const int &, _ArgTypes...);
  _Invoker_type _M_invoker;
};
int apply_v = 41;
void apply(function<void(int &)> handler) {
  handler(apply_v);
  __CPROVER_assert(apply_v == 42, "handler ran through std::function");
}
int main() {
  apply([](int &x) { x += 1; });
}
