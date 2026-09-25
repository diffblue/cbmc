consteval int square(int n)
{
  return n * n;
}

int main()
{
  int x = square(5);
  __CPROVER_assert(x == 25, "consteval square");
}
