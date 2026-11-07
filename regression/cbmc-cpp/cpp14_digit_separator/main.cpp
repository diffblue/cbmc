// C++14 digit separators
int main()
{
  int y = 1'000'000;
  __CPROVER_assert(y == 1000000, "digit separator");
  return 0;
}
