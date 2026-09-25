// C++20 constinit
constinit int x = 42;
int main()
{
  __CPROVER_assert(x == 42, "constinit");
  return 0;
}
