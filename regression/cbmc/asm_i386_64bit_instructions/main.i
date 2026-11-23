// 64-bit instructions are not valid in 32-bit mode: they are not modeled.
int main(void)
{
  unsigned a = 5, d = 0;
  __asm__("cltq" : "+a"(a));
  __asm__("cqto" : "+a"(a), "=d"(d));
  __asm__("movzbq %b1,%0" : "=r"(d) : "q"(a));
  unsigned b = 1;
  __asm__("addl $1,%0" : "+r"(b) : : "cc");
  __CPROVER_assert(b == 2, "32-bit instruction");
  return 0;
}
