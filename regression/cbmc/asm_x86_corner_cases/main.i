// Corner cases of the x86 instruction semantics. "fails" marks properties
// that hardware violates (or that the architecture leaves undefined), so CBMC
// must not prove them.

// asm goto that is interpreted: the statement jumps if and only if v is 0
static int branch(int v)
{
  __asm__ goto("testl %0,%0; jz %l[zero]" : : "r"(v) : "cc" : zero);
  return 0;
zero:
  return 1;
}

int main(void)
{
  // cmpxchgl in 64-bit mode writes only one of accumulator and destination;
  // a 32-bit register write zero-extends, so the other keeps its upper half
  unsigned long long rax = 0x1234567800000005ull; // eax == 5
  unsigned mem = 5;
  __asm__ __volatile__("lock cmpxchgl %2,%1"
                       : "+a"(rax), "+m"(mem)
                       : "r"(7u)
                       : "cc", "memory");
  __CPROVER_assert(mem == 7, "cmpxchg stored");
  __CPROVER_assert(rax == 0x1234567800000005ull, "accumulator unchanged");
  unsigned long long acc = 1;
  unsigned long long dst = 0xabcdef0000000002ull;
  __asm__("cmpxchgl %k2,%k1" : "+a"(acc), "+r"(dst) : "r"(9ull) : "cc");
  __CPROVER_assert(acc == 2, "accumulator loaded");
  __CPROVER_assert(dst == 0xabcdef0000000002ull, "destination unchanged");

  // bsf with a zero source: the destination is undefined (Intel) or unchanged
  // (AMD), including the bits above a 32-bit destination
  unsigned long long r = 0xdead000000000000ull;
  unsigned zero = 0;
  __asm__("bsfl %1,%k0" : "+r"(r) : "rm"(zero) : "cc");
  __CPROVER_assert((r >> 32) == 0, "bsf zero-extends"); // fails

  // shifts by more than the width and address arithmetic that wraps are
  // defined on the hardware: no undefined-behaviour checks apply
  unsigned x = 1;
  __asm__("shlb $20,%b0" : "+q"(x) : : "cc");
  __CPROVER_assert((x & 0xff) == 0, "shlb by 20");
  unsigned long long a, b = 0x4000000000000000ull;
  __asm__("leaq (,%1,4),%0" : "=r"(a) : "r"(b));
  __CPROVER_assert(a == 0, "lea wraps");

  // an array operand in a register is the address of its first element
  char buf[4] = {0};
  __asm__ volatile("movb $1,(%0)" : : "r"(buf) : "memory");
  __CPROVER_assert(buf[0] == 1, "array operand");

  // a register variable bound to a register that the template writes
  register unsigned long long reg asm("rax") = 5;
  __asm__ volatile("addq $1, %%rax" : "+r"(reg));
  __CPROVER_assert(reg == 5, "register variable"); // fails

  __CPROVER_assert(branch(0) == 1, "asm goto jumps");
  __CPROVER_assert(branch(5) == 0, "asm goto falls through");

  return 0;
}
