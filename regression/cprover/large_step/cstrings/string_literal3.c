int main()
{
  char *p = "0123";
  __CPROVER_assert(__CPROVER_r_ok(p), "property 1"); // passes
  __CPROVER_assert(__CPROVER_w_ok(p), "property 2"); // fails
  return 0;
}
