// Corner cases of the AArch64 instruction semantics. "fails" marks
// properties that the architecture permits to be violated, so CBMC must not
// prove them.
static unsigned long add_ll_sc(unsigned long *p, unsigned long v)
{
  unsigned long result;
  unsigned int status;
  __asm__ volatile(
    "1: ldxr %0, [%2]\n"
    " add %0, %0, %3\n"
    " stxr %w1, %0, [%2]\n"
    " cbnz %w1, 1b"
    : "=&r"(result), "=&r"(status)
    : "r"(p), "r"(v)
    : "memory");
  return result;
}

int main(void)
{
  // msr nzcv writes the flags, mrs nzcv reads them
  unsigned long a = 0, r;
  __asm__ volatile("cmp %1, %1\n msr nzcv, xzr\n cset %w0, eq"
                   : "=r"(r)
                   : "r"(a)
                   : "cc");
  __CPROVER_assert(r == 0, "msr nzcv clears Z");
  unsigned long flags;
  __asm__ volatile("cmp %1, %1\n mrs %0, nzcv" : "=r"(flags) : "r"(a) : "cc");
  __CPROVER_assert(flags == 0x60000000ul, "mrs nzcv after equality");

  // a load-exclusive/store-exclusive loop retries until the store succeeds
  unsigned long counter = 40;
  __CPROVER_assert(add_ll_sc(&counter, 2) == 42, "ll/sc result");
  __CPROVER_assert(counter == 42, "ll/sc stored");

  // a store-exclusive without a load-exclusive in the statement may succeed
  // (if a load-exclusive executed before) or fail
  unsigned long m = 1, v = 42;
  unsigned int res;
  __asm__ volatile("stxr %w0, %2, [%1]"
                   : "=&r"(res)
                   : "r"(&m), "r"(v)
                   : "memory");
  __CPROVER_assert(m == 42, "store-exclusive stores"); // fails
  __CPROVER_assert(m == 1, "store-exclusive fails");   // fails
  __CPROVER_assert((res == 0) == (m == 42), "status matches the store");

  // after clrex, a store-exclusive fails
  m = 1;
  __asm__ volatile("clrex\n stxr %w0, %2, [%1]"
                   : "=&r"(res)
                   : "r"(&m), "r"(v)
                   : "memory");
  __CPROVER_assert(m == 1 && res == 1, "store-exclusive after clrex");

  // a register variable bound to a register that the template writes
  register unsigned long x0 __asm__("x0") = 5;
  __asm__ volatile("add x0, x0, #1" : "+r"(x0));
  __CPROVER_assert(x0 == 5, "register variable"); // fails

  return 0;
}
