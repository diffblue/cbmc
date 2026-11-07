// C++11 nested member template instantiation
template <typename T>
struct Outer
{
  template <typename U>
  struct Inner
  {
    T a;
    U b;
  };
};

int main()
{
  Outer<int>::Inner<double> x;
  x.a = 42;
  __CPROVER_assert(x.a == 42, "nested member template");
  return 0;
}
