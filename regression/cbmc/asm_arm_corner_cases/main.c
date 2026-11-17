// Corner cases of the AArch32 instruction semantics. "fails" marks
// properties that the architecture permits to be violated, so CBMC must not
// prove them.
static unsigned add_ll_sc(unsigned *p, unsigned v)
{
  unsigned result, status;
  __asm__ volatile(
    "1: ldrex %0, [%2]\n"
    " add %0, %0, %3\n"
    " strex %1, %0, [%2]\n"
    " teq %1, #0\n"
    " bne 1b"
    : "=&r"(result), "=&r"(status)
    : "r"(p), "r"(v)
    : "cc", "memory");
  return result;
}

int x;

int main(void)
{
  unsigned a = 0, r, zero = 0;

  // msr writes the flags, mrs reads them
  r = 0;
  __asm__ volatile("cmp %1, %1\n msr APSR_nzcvq, %2\n it eq\n moveq %0, #1"
                   : "+r"(r)
                   : "r"(a), "r"(zero)
                   : "cc");
  __CPROVER_assert(r == 0, "msr clears Z");
  unsigned flags;
  __asm__ volatile("cmp %1, %1\n mrs %0, APSR" : "=r"(flags) : "r"(a) : "cc");
  __CPROVER_assert((flags & 0xf0000000u) == 0x60000000u, "mrs after equality");

  // an IT block of four instructions
  r = 0;
  __asm__ volatile(
    "cmp %1, #0\n itttt eq\n addeq %0, %0, #1\n addeq %0, %0, #1\n"
    " addeq %0, %0, #1\n addeq %0, %0, #1"
    : "+r"(r)
    : "r"(a)
    : "cc");
  __CPROVER_assert(r == 4, "it block");

  // a load-exclusive/store-exclusive loop retries until the store succeeds
  unsigned counter = 40;
  __CPROVER_assert(add_ll_sc(&counter, 2) == 42, "ll/sc result");
  __CPROVER_assert(counter == 42, "ll/sc stored");

  // a store-exclusive without a load-exclusive in the statement may succeed
  // (if a load-exclusive executed before) or fail
  unsigned m = 1, v = 42, res;
  __asm__ volatile("strex %0, %2, [%1]"
                   : "=&r"(res)
                   : "r"(&m), "r"(v)
                   : "memory");
  __CPROVER_assert(m == 42, "store-exclusive stores"); // fails
  __CPROVER_assert(m == 1, "store-exclusive fails");   // fails
  __CPROVER_assert((res == 0) == (m == 42), "status matches the store");

  // after clrex, a store-exclusive fails
  m = 1;
  __asm__ volatile("clrex\n strex %0, %2, [%1]"
                   : "=&r"(res)
                   : "r"(&m), "r"(v)
                   : "memory");
  __CPROVER_assert(m == 1 && res == 1, "store-exclusive after clrex");

  // a conditional store-exclusive that does not execute leaves the monitor
  // set, so that the next one may succeed
  m = 1;
  __asm__ volatile(
    "ldrex %0, [%1]\n cmp %3, #0\n ite eq\n strexeq %0, %2, [%1]\n"
    " strexne %0, %2, [%1]"
    : "=&r"(res)
    : "r"(&m), "r"(v), "r"(v)
    : "cc", "memory");
  __CPROVER_assert(res == 1, "conditional store-exclusive"); // fails
  __CPROVER_assert(
    (res == 0) == (m == 42), "status matches the conditional store");

  // shifts by register use the bottom byte of the register
  unsigned s32 = 32, s33 = 0x121, s40 = 40, big = 0x80000001u;
  unsigned lsl, lsr, asr, ror;
  __asm__("lsl %0, %4, %5\n lsr %1, %4, %6\n asr %2, %4, %7\n ror %3, %4, %5"
          : "=&r"(lsl), "=&r"(lsr), "=&r"(asr), "=&r"(ror)
          : "r"(big), "r"(s32), "r"(s33), "r"(s40));
  __CPROVER_assert(
    lsl == 0 && lsr == 0 && asr == 0xffffffffu && ror == big, "shifts");

  // 64-bit subtraction with borrow
  unsigned lo, hi;
  __asm__("subs %0, %2, %4\n sbc %1, %3, %5"
          : "=&r"(lo), "=&r"(hi)
          : "r"(0u), "r"(1u), "r"(1u), "r"(0u)
          : "cc");
  __CPROVER_assert(lo == 0xffffffffu && hi == 0, "subs/sbc");

  // bit and byte manipulation
  unsigned w = 0x12345680u, rv16, rb, cz, sb, uh, mw;
  __asm__(
    "rev16 %0, %6\n rbit %1, %6\n clz %2, %7\n sxtb %3, %6\n"
    " uxth %4, %6\n movw %5, #0xbeef\n movt %5, #0xdead"
    : "=&r"(rv16), "=&r"(rb), "=&r"(cz), "=&r"(sb), "=&r"(uh), "=&r"(mw)
    : "r"(w), "r"(0u));
  __CPROVER_assert(
    rv16 == 0x34128056u && rb == 0x016a2c48u && cz == 32, "rev16 rbit clz");
  __CPROVER_assert(
    sb == 0xffffff80u && uh == 0x5680u && mw == 0xdeadbeefu, "ext movw");

  // loads and stores of bytes and halfwords
  unsigned char bytes[4] = {0x80, 0x7f, 0x01, 0x02};
  unsigned lb, lh;
  __asm__ volatile("ldrsb %0, [%2]\n ldrh %1, [%2, #2]\n strb %1, [%2, #1]"
                   : "=&r"(lb), "=&r"(lh)
                   : "r"(bytes)
                   : "memory");
  __CPROVER_assert(
    lb == 0xffffff80u && lh == 0x0201u && bytes[1] == 1, "ldrsb ldrh strb");

  // reading pc is not modeled
  __asm__ volatile("mov %0, pc" : "=r"(r));
  __CPROVER_assert(r == 0, "pc"); // fails

  // In divided syntax (GCC's default for inline assembly in A32 code and
  // for Thumb-1 targets), Thumb-1 add sets the flags; in A32 code and in
  // unified syntax, it does not.
  __asm__("cmp %1, %1\n add %0, %1, #1\n beq 1f\n mov %0, #7\n1:"
          : "=&r"(r)
          : "r"(a)
          : "cc");
  __CPROVER_assert(r == 1, "flags after add in divided syntax"); // fails
  __asm__(
    ".syntax unified\n cmp %1, %1\n add %0, %1, #1\n beq 1f\n"
    " mov %0, #7\n1:"
    : "=&r"(r)
    : "r"(a)
    : "cc");
  __CPROVER_assert(r == 1, "flags after add in unified syntax");

  // a register variable held in a register that the statement does not
  // initialise
  x = 0;
  {
    register int *p __asm__("r1") = &x;
    __asm__ volatile("str %0, [r1]" : : "r"(5), "r"(p) : "memory");
  }
  __CPROVER_assert(x == 0, "store via register variable"); // fails

  // a register variable bound to a register that the template writes
  register unsigned r0 __asm__("r0") = 5;
  __asm__ volatile("add r0, r0, #1" : "+r"(r0));
  __CPROVER_assert(r0 == 5, "register variable"); // fails

  return 0;
}

// Statements whose use of the stack is not modeled. They are not executed,
// as they would break the program.
void unbalanced(void)
{
  __asm__ volatile("push {r4}");
  __asm__ volatile("push {r4}\n1: pop {r4}");
  __asm__ volatile("pop {pc}");
}
