// Regression for [temp.deduct.partial] forwarding-reference partial
// ordering — the libstdc++ idiom of overloading on `T&` and
// `T&& = delete` to forbid xvalue arguments.
//
// The libstdc++ pattern this fix targets:
//
//   template<typename T>
//     constexpr typename std::add_const<T>::type& as_const(T& t) noexcept;
//
//   template<typename T>
//     void as_const(const T&&) = delete;
//
// or the project-local equivalent in `src/util/as_const.h`:
//
//   template <typename T> const T &as_const(T &value);
//   template <typename T> void as_const(T &&) = delete;
//
// Calling `as_const(s)` with an lvalue `s` should resolve UNAMBIGUOUSLY
// to the first overload — both candidates deduce a parameter type of
// `T&` after reference-collapsing for an lvalue argument, but
// [temp.deduct.partial] specifies that the forwarding-reference
// overload is "less specialized" than the lvalue-reference overload
// for an lvalue argument.  Without this rule, CBMC's distance-based
// disambiguation tied both candidates and reported
//
//   symbol 'as_const' does not uniquely resolve:
//     symbol void (struct S &) (file ... line N)         // T&& deleted
//     symbol const struct S & (struct S &) (file ... line M) // T&
//
// breaking every translation unit that included `<utility>` or
// `src/util/as_const.h` and exercised the call.

template <typename T>
const T &as_const(T &v)
{
  return static_cast<const T &>(v);
}

template <typename T>
void as_const(T &&) = delete;

struct S
{
  int x;
};

int main()
{
  S s;
  s.x = 42;
  const S &cs = as_const(s);
  (void)cs;
  return 0;
}
