static void foo(int x)
{
  __CPROVER_assert(0, "reachable");
}
