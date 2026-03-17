// C++11: decltype(expr) as base specifier
struct A
{
  int x;
};

struct B : decltype(A{})
{
};

int main()
{
  B b;
  b.x = 42;
  return 0;
}
