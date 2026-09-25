extern "C" void __CPROVER_assert(bool, const char *);
template <bool> using __enable_if_t = int;
template <int __v> struct integral_constant {
  static const int value = __v;
};
template <class...> using __expand_to_true = integral_constant<true>;
template <class... _Pred>
__expand_to_true<__enable_if_t<_Pred::value>...> __and_helper(int);
template <class> integral_constant<false> __and_helper(...);
template <class... _Pred> using _And = decltype(__and_helper<_Pred...>(0));
template <class, class = void>
struct _HasToAddress : integral_constant<false> {};
template <class _Pointer>
struct _HasToAddress<_Pointer, decltype(to_address(_Pointer()))>;
template <class> struct _IsFancyPointer {
  static const bool value = _HasToAddress<int>::value;
};
template <class _Pointer> void __to_address(_Pointer);
template <class _Pointer>
auto to_address(_Pointer __p) -> decltype(__to_address(__p));
int main() {
  __CPROVER_assert(_And<_IsFancyPointer<int>>::value, "conjunction holds");
}
