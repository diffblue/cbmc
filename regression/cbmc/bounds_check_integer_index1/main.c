int main()
{
  __CPROVER_integer arr[3];
  __CPROVER_integer i;
  __CPROVER_assume(i >= 0 && i < 3);
  __CPROVER_integer x = arr[i];
  __CPROVER_assert(1, "reachable");
}
