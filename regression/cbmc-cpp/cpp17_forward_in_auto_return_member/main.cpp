extern "C" void __CPROVER_assert(bool, const char *);
template <class _Tp>
struct remove_reference
{
  using type = _Tp;
};
template <class _Tp>
struct remove_reference<_Tp &>
{
  using type = _Tp;
};
template <class _Tp>
struct remove_reference<_Tp &&>
{
  using type = _Tp;
};
template <class _Tp>
using remove_reference_t = typename remove_reference<_Tp>::type;
namespace std
{
template <class _Tp>
constexpr _Tp &&forward(remove_reference_t<_Tp> &__t) noexcept
{
  return static_cast<_Tp &&>(__t);
}
template <class _Tp>
constexpr _Tp &&forward(remove_reference_t<_Tp> &&__t) noexcept
{
  return static_cast<_Tp &&>(__t);
}
} // namespace std
int sink(int &&x)
{
  return x + 1;
}
struct take_fnt
{
  template <class _Np>
  auto operator()(_Np &&__n) const
  {
    // N5008 [dcl.spec.auto]: deduced return; [forward]: the xvalue
    // must bind the rvalue-reference parameter of sink.
    return sink(std::forward<_Np>(__n));
  }
};
int main()
{
  take_fnt take;
  __CPROVER_assert(take(3) == 4, "forward through auto-return member");
  return 0;
}
