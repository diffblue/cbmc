// Regression test for the conditional-operator null-pointer-
// constant check (see src/ansi-c/c_typecheck_expr.cpp:
// typecheck_expr_trinary).  Before the fix, the type checker
// simplified each operand before calling is_null_pointer(),
// which treated `(void *)((long)argc * 0L)` as a null pointer
// constant — even though the ORIGINAL expression is not an
// integer constant expression (argc is runtime).
//
// The Linux kernel's `__is_constexpr` macro exploits exactly
// this distinction to select between compile-time and runtime
// branches in header-level static checks (e.g. GENMASK_INPUT_
// CHECK in <linux/bits.h>).  Pre-fix, CBMC reported
// __is_constexpr(x) == 1 for every x and broke 6.x kernel
// TU compiles.  See LIM-014 in integration/linux/CBMC_
// LIMITATIONS.md.

#define __is_constexpr(x)                                                      \
  (sizeof(int) == sizeof(*(8 ? ((void *)((long)(x)*0l)) : (int *)8)))

int nondet_int(void);

int main(int argc, char **argv)
{
  // Compile-time constant: the conditional's first branch IS a
  // null pointer constant, so the type is `int *`; dereferenced
  // is int; sizeof(int) == sizeof(int) is true.
  __CPROVER_assert(__is_constexpr(5) == 1, "constant is ICE");

  // Runtime value: the conditional's first branch is NOT an
  // integer constant expression, so the type degenerates to
  // `void *`; dereferenced is `void`; sizeof(void) != sizeof(int)
  // so the macro returns 0.
  __CPROVER_assert(__is_constexpr(argc) == 0, "runtime is not ICE");

  // A dereference is likewise not an ICE leaf (the operand lives
  // inside sizeof, so *p is never evaluated): macro yields 0.
  int *p = &argc;
  __CPROVER_assert(__is_constexpr(*p) == 0, "dereference is not ICE");

  // A function call is not an ICE leaf either (also unevaluated
  // inside sizeof): macro yields 0.
  __CPROVER_assert(__is_constexpr(nondet_int()) == 0, "call is not ICE");

  return 0;
}
