int x, y;

int main(void)
{
  int *px = &x;
  unsigned long c, slot;

  // rcx holds the register variable p, but the statement does not
  // initialise it: the store is approximated
  x = 0;
  {
    register int *p __asm__("rcx") = &x;
    __asm__ volatile("movl %0, (%%rcx)" : : "r"(5), "r"(p) : "memory");
  }
  __CPROVER_assert(x == 0, "store via register variable");

  // rcx initialised from an operand before the store: interpreted
  x = 0;
  __asm__ volatile("mov %0, %%rcx\n movl %1, (%%rcx)"
                   :
                   : "r"(px), "r"(5)
                   : "rcx", "memory");
  __CPROVER_assert(x == 5, "store via initialised register");

  // a forward branch skips the initialisation
  x = 0;
  __asm__ volatile("test %2, %2\n jz 1f\n mov %0, %%rcx\n1: movl %1, (%%rcx)"
                   :
                   : "r"(px), "r"(5), "r"(c)
                   : "rcx", "cc", "memory");
  __CPROVER_assert(x == 0, "initialisation skipped by forward branch");

  // a backward branch makes rcx unknown at the store
  x = 0;
  __asm__ volatile(
    "mov %0, %%rcx\n1: movl %1, (%%rcx)\n rdtsc\n mov %%rax, %%rcx\n"
    " test %2, %2\n jnz 1b"
    :
    : "r"(px), "r"(5), "r"(c)
    : "rax", "rcx", "rdx", "cc", "memory");
  __CPROVER_assert(x == 0, "register made unknown by backward branch");

  // an unknown value stored to memory and loaded as an address
  x = 0;
  __asm__ volatile(
    "rdtsc\n mov %%rax, (%0)\n mov (%0), %%rcx\n movl %1, (%%rcx)"
    :
    : "r"(&slot), "r"(5)
    : "rax", "rcx", "rdx", "memory");
  __CPROVER_assert(x == 0, "unknown address loaded from memory");

  // a loop with known values only: interpreted
  y = 0;
  __asm__ volatile(
    "mov %0, %%rcx\n mov $3, %%edx\n"
    "1: addl $1, (%%rcx)\n dec %%edx\n jnz 1b"
    :
    : "r"(&y)
    : "rcx", "rdx", "cc", "memory");
  __CPROVER_assert(y == 3, "loop with known addresses");

  return 0;
}
