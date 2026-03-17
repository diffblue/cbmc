// Test that constexpr evaluation handles skip statements and
// declarations with initial values in the function body.
struct S
{
  int x;
  constexpr S(int v) : x(v)
  {
  }
};

constexpr int f(int a)
{
  int b = a + 1;
  return b;
}

int main()
{
  S s(f(2));
  return s.x;
}
