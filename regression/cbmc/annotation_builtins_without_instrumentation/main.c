int main()
{
  int x;
  __CPROVER_cover(x == 1);
  __CPROVER_set_must(&x, "flag");
  __CPROVER_set_may(&x, "flag");
  __CPROVER_clear_must(&x, "flag");
  __CPROVER_clear_may(&x, "flag");
  __CPROVER_assert(x == x, "reached");
  __CPROVER_assert(0, "WRONG (must FAIL)");
  return 0;
}
