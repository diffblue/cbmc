// Statements containing an instruction that is not modeled are approximated
// conservatively by the remove_asm pass (see
// doc/cprover-manual/modeling-inline-asm.md): everything they may change is
// assigned a nondeterministic value. Each assertion marked "fails" would hold
// if the statement were dropped.
#include <stdint.h>

int global;
int *global_pointer;

struct S
{
  int *p;
  int v;
};

static void clobber(void)
{
  // pointee is not a local variable of this function
  asm volatile("incl global" ::: "memory");
}

int main(void)
{
  int x = 0, y = 1;
  // output operands
  asm volatile("xchg %0,%1" : "+r"(x), "+r"(y));
  __CPROVER_assert(x == 0, "output operand"); // fails

  // a recognized mfence combined with an unrecognized addl: the recognized
  // instruction does not hide the unrecognized one
  int z = 0;
  asm volatile("mfence; addl $1, %0" : "+m"(z));
  __CPROVER_assert(z == 0, "mixed statement"); // fails

  // the object a pointer operand points to, also via an array that decays
  // to a pointer, a cast to an integer type, or a struct member
  int a[2] = {0, 0};
  asm volatile("movl $1, (%0)" : : "r"(a));
  __CPROVER_assert(a[0] == 0, "array operand"); // fails
  int h = 0;
  asm volatile("movl $1, (%0)" : : "r"((uintptr_t)&h));
  __CPROVER_assert(h == 0, "pointer cast to integer"); // fails
  int k = 0;
  struct S s = {&k, 0};
  asm volatile("movl $1, (%0)" : : "m"(s));
  __CPROVER_assert(k == 0, "pointer member");  // fails
  __CPROVER_assert(s.v == 0, "input operand"); // holds

  // "memory" clobber: objects of static lifetime and what they point to
  int pointee = 0;
  global = 0;
  global_pointer = &pointee;
  clobber();
  __CPROVER_assert(global == 0, "static object");              // fails
  __CPROVER_assert(pointee == 0, "pointee of static pointer"); // fails

  // "memory" clobber: address-taken local variables
  int unaddressed = 0, addressed = 0;
  int *escape = &addressed;
  asm volatile("cli" ::: "memory");
  __CPROVER_assert(addressed == 0, "address-taken local");     // fails
  __CPROVER_assert(unaddressed == 0, "local without address"); // holds

  // an empty statement is a compiler barrier only
  int barrier = 0;
  int *barrier_address = &barrier;
  asm volatile("" ::: "memory");
  __CPROVER_assert(barrier == 0, "empty statement"); // holds

  return 0;
}
