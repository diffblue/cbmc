// C++23 if !consteval
int f()
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
  __CPROVER_assert(f() == 42, "runtime branch taken");
}
