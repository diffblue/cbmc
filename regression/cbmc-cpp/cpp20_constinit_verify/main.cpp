// C++20 constinit
constinit int global = 42;
int main()
{
  __CPROVER_assert(global == 42, "constinit");
  return 0;
}
