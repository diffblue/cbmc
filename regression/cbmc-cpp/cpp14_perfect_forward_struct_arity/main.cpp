extern "C" void __CPROVER_assert(bool, const char *);
template <class _Tp, _Tp>
struct integer_sequence;
template <class...>
struct __perfect_forward_impl;
template <class _Op, unsigned long... _Idx>
struct __perfect_forward_impl<_Op, integer_sequence<unsigned long, _Idx...>>
{
  template <class... _Args>
  auto operator()(_Args... __args) -> decltype(_Op()(_Idx..., __args...));
};
template <class _Op>
using __perfect_forward =
  __perfect_forward_impl<_Op, integer_sequence<unsigned long, 0>>;
template <class _Fn>
struct __bind_back_t : __perfect_forward<_Fn>
{
};
template <class _Fn>
auto __bind_back(_Fn...) -> decltype(__bind_back_t<_Fn>())
{
  return __bind_back_t<_Fn>();
}
struct taket
{
  auto operator()(int __n)
  {
    return __bind_back(*this, __n);
  }
} take;
int main()
{
  auto closure = take(3);
  (void)closure;
  __CPROVER_assert(true, "bind_back from member template resolves");
  return 0;
}
