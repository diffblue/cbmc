extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct rr
{
  using type = T;
};
template <class T>
struct rr<T &>
{
  using type = T;
};
template <class T>
constexpr typename rr<T>::type &&move(T &&t)
{
  return static_cast<typename rr<T>::type &&>(t);
}
// N5008 [expr.type]/1, [expr.unary.op]/1: `static_cast<int *&>(p)' is an
// lvalue of type int *, and `*' applied to it yields the int it points to
// (a shape of the MSVC STL's ranges::iter_move)
template <class T>
decltype(auto) iter_move(T &&v)
{
  return move(*static_cast<T &&>(v));
}
int main()
{
  int x = 1;
  int *p = &x;
  __CPROVER_assert(
    *static_cast<int *&>(p) == 1 && *static_cast<int *&&>(p) == 1 &&
      sizeof(*static_cast<int *&>(p)) == sizeof(int) &&
      __is_same(decltype(iter_move(p)), int &&),
    "dereference of a reference to a pointer");
  __CPROVER_assert(*static_cast<int *&>(p) == 2, "WRONG (must FAIL)");
  return 0;
}
