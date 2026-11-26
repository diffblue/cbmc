// C++20 consteval (immediate function)
consteval int square(int x)
{
  return x * x;
}
int main()
{
  int r = square(5);
  __CPROVER_assert(r == 25, "consteval");
  return 0;
}
