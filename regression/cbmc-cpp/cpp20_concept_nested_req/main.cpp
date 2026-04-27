// Nested requirement: requires { requires has_ref<T>; }
template <class T>
concept has_ref = requires
{
  typename T::reference;
};

template <class T>
concept has_all = requires
{
  typename T::value_type;
  requires has_ref<T>;
};

struct A
{
  using value_type = int;
  using reference = int &;
};
struct B
{
  using value_type = int;
};

template <class T>
struct S
{
  static const int x = 0;
};
template <has_all T>
struct S<T>
{
  static const int x = 1;
};

int main()
{
  __CPROVER_assert(S<A>::x == 1, "A has all");
  __CPROVER_assert(S<B>::x == 0, "B missing reference");
}
