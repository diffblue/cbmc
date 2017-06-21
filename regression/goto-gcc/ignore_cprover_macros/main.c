int main()
{
  unsigned x;
  __CPROVER_assume(x);
  __CPROVER_assert(x, "");
}
