// N5008 [temp.inst]/11, [temp.over]/1: naming a function template with
// explicit template arguments instantiates the declarations of its
// candidates, not their definitions; only the selected one is
// instantiated.  libc++'s std::forward has an rvalue overload whose body
// asserts that A is not an lvalue reference; `fwd<A>(a)...' with A = L &
// selects the lvalue overload.  The front end converted the rvalue
// overload's body too (a probe of the callee while a deferred argument
// was type-checked) and ignored its failed static_assert with a warning.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct rr
{
  typedef T type;
};
template <class T>
struct rr<T &>
{
  typedef T type;
};
template <class T>
struct is_lref
{
  static const bool value = false;
};
template <class T>
struct is_lref<T &>
{
  static const bool value = true;
};
template <class T>
constexpr T &&fwd(typename rr<T>::type &t) noexcept
{
  return static_cast<T &&>(t);
}
template <class T>
constexpr T &&fwd(typename rr<T>::type &&t) noexcept
{
  static_assert(!is_lref<T>::value, "cannot forward an rvalue as an lvalue");
  return static_cast<T &&>(t);
}
template <class F, class... A>
constexpr int inv(F &&f, A &&...a)
{
  return static_cast<F &&>(f)(static_cast<A &&>(a)...);
}
struct L
{
  int k;
  int operator()(int x)
  {
    return x + k;
  }
};
template <class R>
struct wrap
{
  template <class... A>
  static constexpr R call(A &&...a)
  {
    return inv(fwd<A>(a)...);
  }
};
int main()
{
  L l{2};
  int x = 1;
  __CPROVER_assert(
    wrap<int>::call(l, static_cast<int &&>(x)) == 3, "forwarded");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
