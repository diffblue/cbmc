template <typename T>
union Storage
{
  T value;
  char bytes[sizeof(T)];
};

template <typename T>
struct Outer
{
  template <typename U>
  union Inner
  {
    U value;
    char c;
  };

  Inner<T> data;
};

int main()
{
  Storage<int> s;
  s.value = 42;
  __CPROVER_assert(s.value == 42, "union template value");

  Outer<int> o;
  o.data.value = 7;
  __CPROVER_assert(o.data.value == 7, "member union template value");

  return 0;
}
