// A load-exclusive/store-exclusive sequence is atomic; plain loads and
// stores are not.
unsigned long x, y, done;

void t(void)
{
  unsigned long tmp;
  unsigned int status;
  __asm__ volatile(
    "1: ldxr %0, [%2]\n"
    " add %0, %0, #1\n"
    " stxr %w1, %0, [%2]\n"
    " cbnz %w1, 1b"
    : "=&r"(tmp), "=&r"(status)
    : "r"(&x)
    : "memory");
  __asm__ volatile(
    "ldr %0, [%1]\n"
    " add %0, %0, #1\n"
    " str %0, [%1]"
    : "=&r"(tmp)
    : "r"(&y)
    : "memory");
}

int main(void)
{
__CPROVER_ASYNC_1:
  t(), done = 1;
  t();
  __CPROVER_assume(done);
  __CPROVER_assert(x == 2, "ll/sc increment");
  __CPROVER_assert(y == 2, "plain increment"); // fails
  return 0;
}
