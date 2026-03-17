// C++23 if consteval
consteval int compile_time()
{
  return 42;
}
int runtime_or_compile()
{
  if consteval
  {
    return compile_time();
  }
  else
  {
    return 0;
  }
}
int main()
{
  int r = runtime_or_compile();
  __CPROVER_assert(r == 0, "runtime path");
  return 0;
}
