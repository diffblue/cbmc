// N5008 [temp.arg.template]/1: the template-argument for a template
// template-parameter is a template-name, possibly QUALIFIED (`ns::is_ptr',
// `std::is_integral'); [temp.names]/2, [temp.param]/1: a use of the parameter
// with arguments inside the template (`Pred<T>::value') names the bound
// template.  The scope walk that resolves `Pred<T>::' looked the bound
// template up by BASE NAME from the root scope, which does not descend into
// namespaces: every use of a qualified template-name as a template template
// argument failed ("found no match for symbol 'std'" ... "invalid implicit
// conversion from '<<type:>>' to '__CPROVER_bool'").  libc++ variant's
// `__trait<_Types, is_trivially_copy_constructible, is_copy_constructible>'
// is this shape.  The speculative type-prefix resolution of the argument
// also printed a spurious "found no match" for a namespace prefix.
#include <type_traits>
extern "C" void __CPROVER_assert(bool, const char *);

namespace ns
{
template <class T>
struct plain
{
  static constexpr bool value = true;
};
template <class T>
struct is_ptr
{
  static constexpr bool value = false;
};
template <class T>
struct is_ptr<T *>
{
  static constexpr bool value = true;
};
template <class T>
struct is_int
{
  static constexpr bool value = false;
};
template <>
struct is_int<int>
{
  static constexpr bool value = true;
};
} // namespace ns

template <class T, template <class> class Pred>
struct Holds
{
  static constexpr bool value = Pred<T>::value;
};
template <class T, template <class> class Pred>
inline constexpr bool holds_v = Pred<T>::value;
template <class T, template <class> class P1, template <class> class P2>
inline constexpr int which_v = P1<T>::value   ? 1
                               : P2<T>::value ? 2
                                              : 0;
template <template <class> class TT>
struct User
{
  TT<int> p;
};

static_assert(Holds<int, ns::plain>::value, "plain primary");
static_assert(Holds<int, ns::is_int>::value, "explicit specialization");
static_assert(Holds<int *, ns::is_ptr>::value, "partial specialization");
static_assert(
  !Holds<int, ns::is_ptr>::value,
  "partial specialization not matched");
static_assert(holds_v<int, std::is_integral>, "variable template, std::");
static_assert(!holds_v<double, std::is_integral>, "variable template, false");
static_assert(
  which_v<int, std::is_integral, std::is_floating_point> == 1,
  "which int");
static_assert(
  which_v<double, std::is_integral, std::is_floating_point> == 2,
  "which double");

int main()
{
  User<ns::plain> u;
  __CPROVER_assert(u.p.value && Holds<int *, ns::is_ptr>::value, "run time");
  __CPROVER_assert(
    which_v<double, std::is_integral, std::is_floating_point> == 1,
    "WRONG (must FAIL)");
}
