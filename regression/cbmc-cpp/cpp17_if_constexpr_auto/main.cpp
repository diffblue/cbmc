// C++17: if constexpr with auto return type
// The discarded branch may contain ill-formed code for the given type.
#include <cassert>

template <typename T>
struct is_pointer
{
  static constexpr bool value = false;
};

template <typename T>
struct is_pointer<T *>
{
  static constexpr bool value = true;
};

template <typename T>
auto deref(T t)
{
  if constexpr(is_pointer<T>::value)
    return *t;
  else
    return t;
}

int main()
{
  int x = 42;
  int *p = &x;
  int r1 = deref(x);
  int r2 = deref(p);
  assert(r1 == 42);
  assert(r2 == 42);
}
