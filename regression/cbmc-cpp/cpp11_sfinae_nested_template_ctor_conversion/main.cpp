// libstdc++ 11's unique_ptr<U, E>&& converting constructor shape: the
// constraint of a constructor TEMPLATE candidate evaluates an is_convertible
// probe (`test_aux<To>(declval<From>())', [temp.deduct]/8) whose parameter
// copy-initialization needs a further class's converting constructor
// template (default_delete<D> -> default_delete<B>).  That nested
// user-defined conversion is a separate conversion sequence
// ([over.best.ics.general]/4 restricts only the candidate's own parameters)
// and must be considered while a substitution is in progress; it was
// refused, the probe evaluated false, and the constructor was dropped
// ("found no match for symbol").  Header-free replica of the gcc-11
// <type_traits>/<memory> shapes.
extern "C" void __CPROVER_assert(bool, const char *);
template <bool B, class T = void>
struct enable_if
{
};
template <class T>
struct enable_if<true, T>
{
  typedef T type;
};
template <class T>
T &&declval() noexcept;
template <bool v>
struct bool_constant
{
  static constexpr bool value = v;
};
typedef bool_constant<true> true_type;
typedef bool_constant<false> false_type;
template <class From, class To>
class conv_helper
{
  template <class To1>
  static void test_aux(To1) noexcept;
  template <
    class From1,
    class To1,
    class = decltype(test_aux<To1>(declval<From1>()))>
  static true_type test(int);
  template <class, class>
  static false_type test(...);

public:
  typedef decltype(test<From, To>(0)) type;
};
template <class From, class To>
struct is_conv : public conv_helper<From, To>::type
{
};
template <class From, class To>
struct is_ptr_conv
{
  static constexpr bool value = false;
};
struct B
{
  virtual ~B() = default;
};
struct D : B
{
};
template <>
struct is_ptr_conv<const D *, const B *>
{
  static constexpr bool value = true;
};
template <class T>
struct del
{
  del() = default;
  template <
    class U,
    class = typename enable_if<is_ptr_conv<U *, T *>::value>::type>
  del(const del<U> &)
  {
  }
};
struct W
{
  template <
    class E,
    class = typename enable_if<is_conv<E, del<const B>>::value>::type>
  W(E &&)
  {
  }
};
int main()
{
  del<const D> d;
  W w(d);
  __CPROVER_assert(is_conv<del<const D>, del<const B>>::value, "convertible");
  return 0;
}
