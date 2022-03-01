int main()
{
  int *p;
  __CPROVER_assume(__CPROVER_r_ok(p));

  for(int i = 0; i < 10; i++)
  {
    // does not assign p
  }

  __CPROVER_assert(__CPROVER_r_ok(p), "property 1"); // passes
}
