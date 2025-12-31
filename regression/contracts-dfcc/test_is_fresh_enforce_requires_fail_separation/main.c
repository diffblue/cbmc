// clang-format off
int *foo(int *p)
  __CPROVER_requires(__CPROVER_is_fresh(p, sizeof(int)))
  __CPROVER_ensures(__CPROVER_is_fresh(__CPROVER_return_value, sizeof(int)))
// clang-format on
{
  return p;
}

int main()
{
  int *p;
  foo(p);
}
