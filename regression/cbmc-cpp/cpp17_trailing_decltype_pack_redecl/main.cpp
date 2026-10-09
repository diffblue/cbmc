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
template <class _Tp>
struct decay
{
  using type = remove_reference_t<_Tp>;
};
template <class _Tp>
using decay_t = typename decay<_Tp>::type;
namespace std
{
template <class _Tp>
constexpr _Tp &&forward(remove_reference_t<_Tp> &__t) noexcept;
template <class _Tp>
constexpr _Tp &&forward(remove_reference_t<_Tp> &&__t) noexcept;
template <class... _Ts>
struct tuple
{
  int first;
};
template <class... _Ts>
constexpr tuple<_Ts...> forward_as_tuple(_Ts &&...) noexcept;
template <class _B>
struct bbt
{
  _B b;
  template <class _B2>
  bbt(_B2 &&__b) : b(__b.first, 7)
  {
  }
};
template <class _B>
struct bbt<tuple<_B>>
{
  tuple<_B> b;
  template <class _B2>
  bbt(_B2 &&)
  {
    b.first = 7;
  }
  int val() const
  {
    return b.first;
  }
};
template <class... _Args>
auto bb(_Args &&...__args) noexcept -> decltype(bbt<tuple<int>>(
  std::forward_as_tuple(std::forward<_Args>(__args)...)));
template <class... _Args>
auto bb(_Args &&...__args) noexcept -> decltype(bbt<tuple<int>>(
  std::forward_as_tuple(std::forward<_Args>(__args)...)))
{
  return bbt<tuple<int>>(std::forward_as_tuple(std::forward<_Args>(__args)...));
}
} // namespace std
int main()
{
  auto r = std::bb(3);
  __CPROVER_assert(r.val() == 7, "bind_back shape with template-arg pack");
  return 0;
}
