int x, y;

int main(void)
{
  int *px = &x;
  unsigned long c, slot;

  // x1 holds the register variable p, but the statement does not
  // initialise it: the store is approximated
  x = 0;
  {
    register int *p __asm__("x1") = &x;
    __asm__ volatile("str %w0, [x1]" : : "r"(5), "r"(p) : "memory");
  }
  __CPROVER_assert(x == 0, "store via register variable");

  // x1 initialised from an operand before the store: interpreted
  x = 0;
  __asm__ volatile("mov x1, %0\n str %w1, [x1]"
                   :
                   : "r"(px), "r"(5)
                   : "x1", "memory");
  __CPROVER_assert(x == 5, "store via initialised register");

  // a forward branch skips the initialisation
  x = 0;
  __asm__ volatile("cbz %2, 1f\n mov x1, %0\n1: str %w1, [x1]"
                   :
                   : "r"(px), "r"(5), "r"(c)
                   : "x1", "memory");
  __CPROVER_assert(x == 0, "initialisation skipped by forward branch");

  // a backward branch makes x1 unknown at the store
  x = 0;
  __asm__ volatile(
    "mov x1, %0\n1: str %w1, [x1]\n mrs x1, tpidr_el0\n cbnz %2, 1b"
    :
    : "r"(px), "r"(5), "r"(c)
    : "x1", "memory");
  __CPROVER_assert(x == 0, "register made unknown by backward branch");

  // an unknown value stored to memory and loaded as an address
  x = 0;
  __asm__ volatile(
    "mrs x1, tpidr_el0\n str x1, [%0]\n ldr x2, [%0]\n str %w1, [x2]"
    :
    : "r"(&slot), "r"(5)
    : "x1", "x2", "memory");
  __CPROVER_assert(x == 0, "unknown address loaded from memory");

  // a loop with known values only: interpreted
  y = 0;
  __asm__ volatile(
    "mov x1, %0\n mov x3, #3\n"
    "1: ldr w2, [x1]\n add w2, w2, #1\n str w2, [x1]\n"
    " subs x3, x3, #1\n b.ne 1b"
    :
    : "r"(&y)
    : "x1", "x2", "x3", "cc", "memory");
  __CPROVER_assert(y == 3, "loop with known addresses");

  return 0;
}
