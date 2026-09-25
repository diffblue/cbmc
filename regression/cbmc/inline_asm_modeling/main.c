// Each statement below is processed independently by the remove_asm pass.
// This test pins the documented translation of the recognized instructions
// (see doc/cprover-manual/modeling-inline-asm.md) via the goto program shown
// by --show-goto-functions.
int main(void)
{
  unsigned short cw = 0;

  // x86 fences: modeled as calls to the __asm_* fence helpers.
  asm volatile("mfence");
  asm volatile("lfence");
  asm volatile("sfence");

  // ARM barriers: dmb/dsb are full fences, isb is an empty fence.
  asm volatile("dmb");
  asm volatile("dsb");
  asm volatile("isb");

  // Power barriers: sync is a full fence, lwsync omits write-after-read,
  // isync is an empty fence.
  asm volatile("sync");
  asm volatile("lwsync");
  asm volatile("isync");

  // x86 FP control word: writes/reads __CPROVER_rounding_mode via the operand.
  asm volatile("fstcw %0" : "=m"(cw));
  asm volatile("fldcw %0" : : "m"(cw));

  // lock prefix followed by a recognized instruction: atomic section + fence.
  asm volatile("lock; mfence");

  return 0;
}
