#define ARM_BUILTIN_HEADERS \
  "void __breakpoint(int val);\n" \
  "void __cdp(unsigned int coproc, unsigned int ops, unsigned int regs);\n" \
  "void __clrex(void);\n" \
  "unsigned char __clz(unsigned int val);\n" \
  "unsigned int __current_pc(void);\n" \
  "unsigned int __current_sp(void);\n" \
  "int __disable_fiq(void);\n" \
  "int __disable_irq(void);\n" \
  "void __enable_fiq(void);\n" \
  "void __enable_irq(void);\n" \
  "double __fabs(double val);\n" \
  "float __fabs(float val);\n" \
  "void __force_stores(void);\n" \
  "unsigned int __ldrex(volatile void *ptr);\n" \
  "unsigned long long __ldrexd(volatile void *ptr);\n" \
  "unsigned int __ldrt(const volatile void *ptr);\n" \
  "void __memory_changed(void);\n" \
  "void __nop(void);\n" \
  "void __pld();\n" \
  "void __pldw();\n" \
  "void __pli();\n" \
  "void __promise(expr);\n" \
  "int __qadd(int val1, int val2);\n" \
  "int __qdbl(int val);\n" \
  "int __qsub(int val1, int val2);\n" \
  "unsigned int __rbit(unsigned int val);" \
  "unsigned int __rev(unsigned int val);" \
  "unsigned int __return_address(void);" \
  "unsigned int __ror(unsigned int val, unsigned int shift);\n" \
  "void __schedule_barrier(void);\n" \
  "int __semihost(int val, const void *ptr);\n" \
  "void __sev(void);\n" \
  "void __sev(void);\n" \
  "float __sqrtf(float);\n" \
  "int __ssat(int val, unsigned int sat);\n" \
  "int __strex(unsigned int val, volatile void *ptr);\n" \
  "int __strexd(unsigned long long val, volatile void *ptr);\n" \
  "void __strt(unsigned int val, volatile void *ptr);\n" \
  "unsigned int __swp(unsigned int val, volatile void *ptr);\n" \
  "int __usat(unsigned int val, unsigned int sat);\n" \
  "void __wfe(void);\n" \
  "void __wfi(void);\n" \
  "void __yield(void);\n"
