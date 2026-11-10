struct S
{
  template <typename T>
  void foo(T arg)
  {
  }

  template <typename T>
  T bar(T a, T b)
  {
    return a + b;
  }
};

int main()
{
  S s;
  s.foo(1);
  s.foo(3.14);
  int r = s.bar(2, 3);
  __CPROVER_assert(r == 5, "bar(2,3)==5");
  return 0;
}
