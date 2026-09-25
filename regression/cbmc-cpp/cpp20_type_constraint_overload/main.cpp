// N5008 [temp.param]/4: a type-constraint `C T' (or `ns::C T', or
// `C<A> T') on a type template parameter introduces the constraint-expression
// `C<T>' (`C<T, A>') into the template's associated constraints; with
// [temp.constr.decl]/3 and [over.match.viable] a function template whose
// constraints are not satisfied by the deduced arguments is not viable.  The
// front end decided a type-constraint with a structural evaluator over the
// concept body that could not tell `Integral<double>' false: two overloads
// `template<Integral T> g(T)' / `template<Floating T> g(T)' resolved to
// whichever was declared FIRST for every call -- a wrong verdict.  The
// type-constraint is now evaluated as the constraint-expression it stands
// for, through the requires-clause path.
#include <concepts>
#include <type_traits>
extern "C" void __CPROVER_assert(bool, const char *);

template <class T>
concept Integral = std::is_integral_v<T>;
template <class T>
concept Floating = std::is_floating_point_v<T>;
namespace ns
{
template <class T>
concept Small = sizeof(T) <= 2;
}
template <class T, class U>
concept SameAs = std::is_same_v<T, U>;

template <Integral T>
int g(T)
{
  return 1;
}
template <Floating T>
int g(T)
{
  return 2;
}
template <class T>
requires Integral<T> int h(T)
{
  return 1;
}
template <class T>
requires Floating<T> int h(T)
{
  return 2;
}
template <ns::Small T>
int k(T)
{
  return 2;
}
template <class T>
requires(sizeof(T) > 2) int k(T)
{
  return 8;
}
template <std::integral T>
int s(T)
{
  return 1;
}
template <std::floating_point T>
int s(T)
{
  return 2;
}
// a type-constraint with its own arguments: `SameAs<T> U' is `SameAs<U, T>'
template <class T, SameAs<T> U>
T add(T a, U b)
{
  return a + b;
}

int main()
{
  __CPROVER_assert(g(1) == 1 && g(1.0) == 2, "type-constraint overloads");
  __CPROVER_assert(h(1) == 1 && h(1.0) == 2, "requires-clause overloads");
  __CPROVER_assert(k((short)1) == 2 && k(1.0) == 8, "qualified concept");
  __CPROVER_assert(s(1) == 1 && s(1.0) == 2, "standard concepts");
  __CPROVER_assert(add(1, 2) == 3, "type-constraint with arguments");
  __CPROVER_assert(g(1.0) == 1, "WRONG (must FAIL)");
}
