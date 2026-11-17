int add(int a, int b) __CPROVER_requires(a >= 0 && b >= 0)
  __CPROVER_ensures(__CPROVER_return_value == a + b);

int add(int a, int b)
{
  return a + b;
}

int main()
{
  int x = add(1, 2);
  __CPROVER_assert(x == 3, "add works");
}
