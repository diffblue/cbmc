// An atomic instruction is an atomic section on its own, not the whole
// statement: the read-modify-write of x by plain instructions can race.
unsigned x, y, z, dummy;

void t(void)
{
  __asm__ __volatile__(
    "movl %0,%%eax\n\t"
    "incl %%eax\n\t"
    "movl %%eax,%0\n\t"
    "lock orl $0,%1"
    : "+m"(x), "+m"(dummy)
    :
    : "eax", "cc", "memory");
  __asm__ __volatile__("lock incl %0" : "+m"(y) : : "cc", "memory");
}

int main(void)
{
__CPROVER_ASYNC_1:
  t(), z = 1;
  t();
  __CPROVER_assume(z);
  __CPROVER_assert(x == 2, "plain read-modify-write"); // fails
  __CPROVER_assert(y == 2, "locked increment");
  return 0;
}
