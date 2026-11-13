// C++11 alignas as member specifier
struct S
{
  alignas(16) int x;
  alignas(double) char buf[32];
};

int main()
{
  S s;
  s.x = 42;
  return 0;
}
