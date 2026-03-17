// Test that brace-enclosed return values work for POD structs
// (aggregate initialization in return statements).
struct S
{
  int x;
};

struct T
{
  int a;
  int b;
};

S f(int v)
{
  return {v};
}

T g(int a, int b)
{
  return {a, b};
}

int main()
{
  S s = f(42);
  __CPROVER_assert(s.x == 42, "single member");
  T t = g(1, 2);
  __CPROVER_assert(t.a == 1, "first member");
  __CPROVER_assert(t.b == 2, "second member");
  return 0;
}
