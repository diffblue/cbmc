// C++14 binary literals
int main()
{
  int x = 0b1010;
  __CPROVER_assert(x == 10, "binary literal");
  return 0;
}
