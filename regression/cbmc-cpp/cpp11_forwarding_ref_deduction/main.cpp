// Per [temp.deduct.call]/3: a forwarding reference is an rvalue
// reference to a cv-unqualified template parameter.  If the argument
// is an lvalue, type deduction uses 'lvalue reference to A' in place
// of A; for an rvalue argument, A is used unchanged.
//
// This matters for std::forward which relies on reference collapsing:
//   T&& -> & && -> &     (for T = A&)
//   T&& -> && &&  -> &&   (for T = A)
//
// CBMC's deduction must follow the rule so that downstream
// instantiations pick the correct overload.

#include <type_traits>

template <typename T>
struct deduced
{
  // Extract what T was deduced to be.
  using type = T;
};

template <typename T>
auto deduce(T &&) -> deduced<T>;

int main()
{
  int lv = 0;
  const int clv = 0;

  // Lvalue -> T is 'int&'
  static_assert(
    std::is_same<decltype(deduce(lv))::type, int &>::value,
    "lvalue -> T = int&");

  // const lvalue -> T is 'const int&'
  static_assert(
    std::is_same<decltype(deduce(clv))::type, const int &>::value,
    "const lvalue -> T = const int&");

  // Rvalue -> T is 'int' (not int&&)
  static_assert(
    std::is_same<decltype(deduce(0))::type, int>::value, "rvalue -> T = int");

  return 0;
}
