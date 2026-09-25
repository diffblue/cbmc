template <typename T>
struct S
{
  typedef T iterator;
  auto f() -> iterator;
};

template <typename T>
auto S<T>::f() -> iterator
{
  return T();
}

int main()
{
  S<int> s;
  return s.f();
}
