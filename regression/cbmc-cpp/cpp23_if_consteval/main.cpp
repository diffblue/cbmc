// C++23 if consteval / if !consteval
constexpr int f()
{
  if consteval
  {
    return 1;
  }
  else
  {
    return 2;
  }
}

int g()
{
  if !consteval
  {
    return 42;
  }
  else
  {
    return 0;
  }
}

int main()
{
  __CPROVER_assert(f() == 2, "if consteval takes else");
  __CPROVER_assert(g() == 42, "if !consteval takes if");
}
