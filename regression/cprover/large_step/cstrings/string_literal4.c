int main()
{
  char *p = "0123";
  __CPROVER_assert(__CPROVER_OBJECT_SIZE(p) == 5, "property 1"); // passes
  __CPROVER_assert(__CPROVER_LIVE_OBJECT(p), "property 2");      // passes
  return 0;
}
