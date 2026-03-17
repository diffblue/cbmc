// C++23 auto(x) decay copy
int main()
{
  int a = 5;
  auto b = auto(a);
  __CPROVER_assert(b == 5, "auto decay");
  return 0;
}
