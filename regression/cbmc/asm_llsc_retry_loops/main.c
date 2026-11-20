// Retry loops of load-exclusive/store-exclusive sequences (AArch64)
unsigned long x;

int main(void)
{
  unsigned long result, attempts = 0;
  unsigned int status;

  // a restartable retry loop: a failed attempt has no effect
  x = 40;
  __asm__ volatile(
    "1: ldxr %0, [%2]\n"
    " add %0, %0, #2\n"
    " stxr %w1, %0, [%2]\n"
    " cbnz %w1, 1b"
    : "=&r"(result), "=&r"(status)
    : "r"(&x)
    : "memory");
  __CPROVER_assert(result == 42 && x == 42, "restartable loop");

  // counting the attempts reads a register before writing it
  x = 40;
  __asm__ volatile(
    "1: add %2, %2, #1\n"
    " ldxr %0, [%3]\n"
    " add %0, %0, #2\n"
    " stxr %w1, %0, [%3]\n"
    " cbnz %w1, 1b"
    : "=&r"(result), "=&r"(status), "+r"(attempts)
    : "r"(&x)
    : "memory");
  __CPROVER_assert(x == 42, "counting loop");
  __CPROVER_assert(attempts == 1, "one attempt"); // fails

  // a branch that is taken when the store succeeds is not a retry
  x = 40;
  attempts = 0;
  __asm__ volatile(
    "1: add %2, %2, #1\n"
    " ldxr %0, [%3]\n"
    " stxr %w1, %0, [%3]\n"
    " cbz %w1, 1b"
    : "=&r"(result), "=&r"(status), "+r"(attempts)
    : "r"(&x)
    : "memory");
  __CPROVER_assert(attempts == 1, "branch on success"); // fails

  return 0;
}
