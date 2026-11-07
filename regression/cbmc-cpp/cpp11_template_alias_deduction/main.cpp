// C++11 template alias in function template argument deduction
template <typename T>
using Ptr = T *;

template <typename T>
T deref(Ptr<T> p)
{
  return *p;
}

int main()
{
  int x = 42;
  __CPROVER_assert(deref(&x) == 42, "template alias deduction");
  return 0;
}
