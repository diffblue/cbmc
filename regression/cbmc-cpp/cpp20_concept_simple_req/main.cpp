// Simple requirement: requires(T t) { ++t; }
template <class T>
concept incrementable = requires(T t)
{
  ++t;
};

struct A
{
  A &operator++();
};
struct B
{
};

template <class T>
struct S
{
  static const int x = 0;
};
template <incrementable T>
struct S<T>
{
  static const int x = 1;
};

int main()
{
  __CPROVER_assert(S<A>::x == 1, "A is incrementable");
  __CPROVER_assert(S<B>::x == 0, "B is not incrementable");
}
