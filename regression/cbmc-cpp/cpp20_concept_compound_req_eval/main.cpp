// Compound requirement: requires(T t) { { *t } -> same_as<int&>; }
#include <type_traits>
template <class T, class U>
concept same_as_test = __is_same(T, U);

template <class T>
concept deref_to_int = requires(T t)
{
  {
    *t
    } -> same_as_test<int &>;
};

struct A
{
  int &operator*();
};
struct B
{
  double &operator*();
};

template <class T>
struct S
{
  static const int x = 0;
};
template <deref_to_int T>
struct S<T>
{
  static const int x = 1;
};

int main()
{
  __CPROVER_assert(S<A>::x == 1, "A derefs to int&");
  __CPROVER_assert(S<B>::x == 0, "B derefs to double&");
}
