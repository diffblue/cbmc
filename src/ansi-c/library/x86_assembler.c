
/* FUNCTION: __asm_fnstcw */

extern int __CPROVER_rounding_mode;

void __asm_fnstcw(void *dest)
{
  // the rounding mode is bits 10 and 11 in the control word
  *(unsigned short *)dest = __CPROVER_rounding_mode << 10;
}

/* FUNCTION: __asm_fstcw */

extern int __CPROVER_rounding_mode;

void __asm_fstcw(void *dest)
{
  // the rounding mode is bits 10 and 11 in the control word
  *(unsigned short *)dest = __CPROVER_rounding_mode << 10;
}

/* FUNCTION: __asm_fldcw */

extern int __CPROVER_rounding_mode;

void __asm_fldcw(void *src)
{
  // the rounding mode is bits 10 and 11 in the control word
  __CPROVER_rounding_mode = ((*(const unsigned short *)src) >> 10) & 3;
}

/* FUNCTION: __asm_stmxcsr */

extern int __CPROVER_rounding_mode;
unsigned int __VERIFIER_nondet_unsigned_int(void);

void __asm_stmxcsr(void *dest)
{
  // The rounding mode is bits 13 and 14 in the SSE control and status
  // register. The other bits (exception flags and masks, flush-to-zero,
  // denormals-are-zero) are not modeled.
  *(unsigned int *)dest = (__VERIFIER_nondet_unsigned_int() & ~0x6000u) |
                          ((unsigned int)__CPROVER_rounding_mode << 13);
}

/* FUNCTION: __asm_ldmxcsr */

extern int __CPROVER_rounding_mode;

void __asm_ldmxcsr(void *src)
{
  // the rounding mode is bits 13 and 14 in the SSE control and status
  // register
  __CPROVER_rounding_mode = ((*(const unsigned int *)src) >> 13) & 3;
}

/* FUNCTION: __asm_mfence */

void __asm_mfence(void)
{
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
}

/* FUNCTION: __asm_sfence */

void __asm_sfence(void)
{
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
}

/* FUNCTION: __asm_lfence */

void __asm_lfence(void)
{
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
}
