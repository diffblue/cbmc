// Retry loops of load-exclusive/store-exclusive sequences (AArch32)
unsigned x;

int main(void)
{
  unsigned result, status;

  // with teq and bne, as in the Linux kernel's atomics
  x = 40;
  __asm__ volatile(
    "1: ldrex %0, [%2]\n"
    " add %0, %0, #2\n"
    " strex %1, %0, [%2]\n"
    " teq %1, #0\n"
    " bne 1b"
    : "=&r"(result), "=&r"(status)
    : "r"(&x)
    : "cc", "memory");
  __CPROVER_assert(result == 42 && x == 42, "teq/bne loop");

  // with cmp and bne
  x = 40;
  __asm__ volatile(
    "1: ldrex %0, [%2]\n"
    " orr %0, %0, #1\n"
    " strex %1, %0, [%2]\n"
    " cmp %1, #0\n"
    " bne 1b"
    : "=&r"(result), "=&r"(status)
    : "r"(&x)
    : "cc", "memory");
  __CPROVER_assert(x == 41, "cmp/bne loop");

  // a store to memory before the load makes an attempt observable
  unsigned stores = 0;
  x = 40;
  __asm__ volatile(
    "1: ldr %0, [%3]\n"
    " add %0, %0, #1\n"
    " str %0, [%3]\n"
    " ldrex %0, [%2]\n"
    " strex %1, %0, [%2]\n"
    " teq %1, #0\n"
    " bne 1b"
    : "=&r"(result), "=&r"(status)
    : "r"(&x), "r"(&stores)
    : "cc", "memory");
  __CPROVER_assert(stores == 1, "store in the loop"); // fails

  return 0;
}
