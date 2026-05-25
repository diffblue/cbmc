template <typename T>
struct Container
{
  T value;
};

template <template <typename> class C, typename T>
T get_value(C<T> c)
{
  return c.value;
}

int main()
{
  Container<int> c;
  c.value = 42;
  int r = get_value(c);
  __CPROVER_assert(r == 42, "template template deduction");
  return 0;
}
