// C++23 explicit object parameter in lambda
int main()
{
  auto add = [](this auto self, int a, int b) -> int { return a + b; };
  int r = add(1, 2);
  __CPROVER_assert(r == 3, "deducing this lambda");
  return 0;
}
