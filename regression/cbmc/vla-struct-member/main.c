unsigned nondet_unsigned(void);

int main()
{
  unsigned n = nondet_unsigned();
  __CPROVER_assume(n > 0 && n < 4);

  // GCC extension: arrays of non-constant size as struct members (also not as
  // the last member)
  struct S
  {
    int a[n];
    int b;
  } s;
  struct T
  {
    int b;
    int a[n];
  } t;

  s.b = (int)n;
  s.a[0] = 1;
  t.b = (int)n;
  t.a[n - 1] = 2;

  __CPROVER_assert(s.b == n, "member after array");
  __CPROVER_assert(s.a[0] == 1, "array member");
  __CPROVER_assert(t.b == n, "member before array");
  __CPROVER_assert(t.a[n - 1] == 2, "trailing array member");
  __CPROVER_assert(s.b != 2, "expected to fail");
  return 0;
}
