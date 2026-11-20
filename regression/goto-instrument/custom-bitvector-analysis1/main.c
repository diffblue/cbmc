int main()
{
  int x;
  int *p = &x;
  __CPROVER_set_must(&x, "tainted");
  __CPROVER_assert(__CPROVER_get_must(&x, "tainted"), "set");
  __CPROVER_assert(__CPROVER_get_must(p, "tainted"), "set, via p");
  __CPROVER_clear_must(&x, "tainted");
  __CPROVER_assert(__CPROVER_get_must(&x, "tainted"), "cleared");
  __CPROVER_assert(!__CPROVER_get_may(&x, "other"), "never set");
  return 0;
}
