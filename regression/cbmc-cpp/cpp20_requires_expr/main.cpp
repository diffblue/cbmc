// C++20 requires expression in concept
template <typename T>
concept Addable = requires(T a, T b)
{
  a + b;
};

template <Addable T>
T add(T a, T b)
{
  return a + b;
}

int main()
{
  int r = add(1, 2);
  __CPROVER_assert(r == 3, "requires expr");
  return 0;
}
