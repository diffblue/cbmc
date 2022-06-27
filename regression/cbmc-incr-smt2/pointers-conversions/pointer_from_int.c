int main()
{
  int *p = (int *)4;
  __CPROVER_allocated_memory(4, sizeof(int));

  __CPROVER_assert(p == 4, "p == 4: expected success");
  __CPROVER_assert(p != 0, "p != 0: expected success");

  p = (int *)0x1020304;
  __CPROVER_assert(p == 0x1020304, "p == 0x1020304: expected success");
  __CPROVER_assert(p != 0, "p != 0: expected success");
  __CPROVER_assert(p == 0, "p != 0: expected failure");
}
