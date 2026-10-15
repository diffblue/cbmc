// N5008 [temp.spec.partial.match]/2: a partial specialization matches only
// if the deduced arguments satisfy its associated constraints, including
// the type-constraints of its template parameters ([temp.param]/4:
// `C T' introduces `C<T>')
#include <concepts>
extern "C" void __CPROVER_assert(bool, const char *);

// a concept defined through a variable template
template <class T>
constexpr bool is_small = sizeof(T) <= 2;
template <class T>
concept small = is_small<T>;

// libstdc++ <format>'s formatter: integral and floating-point partial
// specializations, each with a member template of the same name
template <class T, class C>
struct fmt;
template <std::integral T, class C>
struct fmt<T, C>
{
  int id() const
  {
    return 1;
  }
  template <class O>
  int format(T, O) const
  {
    return 10;
  }
};
template <std::floating_point T, class C>
struct fmt<T, C>
{
  int id() const
  {
    return 2;
  }
  template <class O>
  int format(T, O) const
  {
    return 20;
  }
};

template <class T>
struct size_class
{
  static constexpr int value = 0;
};
template <small T>
struct size_class<T>
{
  static constexpr int value = 1;
};

// variable templates ([temp.spec.partial.general]/1)
template <class T>
constexpr int kind = 0;
template <small T>
constexpr int kind<T> = 1;
template <class T>
constexpr int req = 0;
template <class T>
requires small<T> constexpr int req<T> = 2;

int main()
{
  fmt<double, char> fd;
  fmt<int, char> fi;
  __CPROVER_assert(fd.id() == 2, "floating-point specialization");
  __CPROVER_assert(fd.format(1.5, 0) == 20, "its member template");
  __CPROVER_assert(fi.id() == 1, "integral specialization");
  __CPROVER_assert(fi.format(3, 0) == 10, "its member template too");
  __CPROVER_assert(size_class<short>::value == 1, "satisfied");
  __CPROVER_assert(size_class<long>::value == 0, "unsatisfied: primary");
  __CPROVER_assert(kind<char> == 1 && kind<long> == 0, "variable template");
  __CPROVER_assert(req<char> == 2 && req<long> == 0, "requires-clause");
  __CPROVER_assert(fd.id() == 1, "WRONG (must FAIL)");
}
