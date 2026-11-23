// A load-exclusive/store-exclusive sequence is atomic; plain loads and
// stores are not.
unsigned x, y, done;

void t(void)
{
  unsigned tmp, status;
  __asm__ volatile(
    "1: ldrex %0, [%2]\n"
    " add %0, %0, #1\n"
    " strex %1, %0, [%2]\n"
    " teq %1, #0\n"
    " bne 1b"
    : "=&r"(tmp), "=&r"(status)
    : "r"(&x)
    : "cc", "memory");
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
