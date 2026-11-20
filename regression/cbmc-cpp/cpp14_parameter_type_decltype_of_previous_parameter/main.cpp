extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct remove_reference
{
  using type = T;
};
template <class T>
struct remove_reference<T &>
{
  using type = T;
};
template <class T>
struct remove_reference<T &&>
{
  using type = T;
};
template <class T>
constexpr typename remove_reference<T>::type &&move(T &&t) noexcept
{
  return static_cast<typename remove_reference<T>::type &&>(t);
}
template <class Iter>
constexpr Iter unwrap_iter(Iter i)
{
  return i;
}
template <class Orig, class Iter>
constexpr Orig rewrap_iter(Orig, Iter i)
{
  return i;
}
template <class Iter, class Sent>
struct unwrap_range_impl
{
  static constexpr auto rewrap(const Iter &, Iter iter)
  {
    return iter;
  }
};
template <class Iter>
struct unwrap_range_impl<Iter, Iter>
{
  // the second parameter's type names the first parameter
  static constexpr auto
  rewrap(Iter orig_iter, decltype(unwrap_iter(orig_iter)) iter)
  {
    return rewrap_iter(move(orig_iter), move(iter));
  }
};
template <class Sent, class Iter, class Unwrapped>
constexpr Iter rewrap_range(Iter orig_iter, Unwrapped iter)
{
  return unwrap_range_impl<Iter, Sent>::rewrap(move(orig_iter), move(iter));
}
int main()
{
  const char text[] = "abc";
  const char *r = rewrap_range<const char *>(text, text + 2);
  __CPROVER_assert(
    r == text + 2,
    "parameter type spelled with decltype of a previous parameter");
  __CPROVER_assert(r == text, "WRONG (must FAIL)");
}
