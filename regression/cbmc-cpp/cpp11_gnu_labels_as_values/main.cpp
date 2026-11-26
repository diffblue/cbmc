extern "C" void __CPROVER_assert(bool, const char *);
// GNU labels as values and computed goto (a dispatch table, as in an
// interpreter loop)
int run(const int *program, int n)
{
  static const void *const table[] = {&&add, &&twice, &&stop};
  int acc = 0, pc = 0;
  goto *table[program[pc]];
add:
  ++acc;
  if(++pc < n)
    goto *table[program[pc]];
  return acc;
twice:
  acc *= 2;
  if(++pc < n)
    goto *table[program[pc]];
  return acc;
stop:
  return -acc;
}
int main()
{
  int p1[] = {0, 1, 0, 1};
  __CPROVER_assert(run(p1, 4) == 6, "dispatch");
  int p2[] = {0, 2};
  __CPROVER_assert(run(p2, 2) == -1, "stop");
  void *target = &&end;
  goto *target;
  __CPROVER_assert(false, "skipped");
end:
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
