// Test that bool(expr) is correctly parsed as a functional cast
// rather than a function type when used in a template argument.

template <typename T>
struct S
{
  static const bool value = true;
};

template <bool>
struct enable_if
{
  typedef int type;
};

template <typename T>
typename enable_if<bool(S<T>::value)>::type foo()
{
  return 0;
}

int main()
{
  foo<int>();
}
