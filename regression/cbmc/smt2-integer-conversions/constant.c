int main()
{
  __CPROVER_integer m = -1;
  unsigned u = (unsigned)m;
  __CPROVER_assert(u == 0xFFFFFFFFu, "wraps");
  return 0;
}
