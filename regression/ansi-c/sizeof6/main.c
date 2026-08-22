int main()
{
  long long i;
#ifndef _MSC_VER
  // A direct null pointer constant: the first branch is `void *` and a null
  // pointer constant, so the conditional has type `int *`; *... is `int`.
  _Static_assert(sizeof(int) == sizeof(*(1 ? ((void *)(0ll)) : (int *)1)), "");

  // Integer constant expressions that evaluate to 0 are null pointer constants
  // irrespective of which constant operators are used to build them. GCC and
  // Clang treat all of the following as null pointer constants (so the
  // conditional has type `int *`). In particular this must not depend on the
  // operator: recognising only multiplication/addition wrongly rejects
  // subtraction, division, and shifts.
  _Static_assert(
    sizeof(int) == sizeof(*(1 ? ((void *)(5 * 0)) : (int *)1)), "");
  _Static_assert(
    sizeof(int) == sizeof(*(1 ? ((void *)(1 - 1)) : (int *)1)), "");
  _Static_assert(
    sizeof(int) == sizeof(*(1 ? ((void *)(2 / 2 - 1)) : (int *)1)), "");
  _Static_assert(
    sizeof(int) == sizeof(*(1 ? ((void *)(0 << 3)) : (int *)1)), "");

  // Expressions involving the runtime variable i simplify to 0, but are NOT
  // integer constant expressions. GCC and Clang do not treat them as null
  // pointer constants, so the conditional has type `void *` and sizeof(*...)
  // (sizeof(void), treated as 1) differs from sizeof(int).
  _Static_assert(
    sizeof(int) != sizeof(*(1 ? ((void *)(i * 0)) : (int *)1)), "");
  _Static_assert(
    sizeof(int) != sizeof(*(1 ? ((void *)(i - i)) : (int *)1)), "");
  _Static_assert(
    sizeof(int) != sizeof(*(1 ? ((void *)(i ? 0ll : 0ll)) : (int *)1)), "");
  _Static_assert(
    sizeof(int) != sizeof(*(1 ? ((void *)(0 ? i : 0ll)) : (int *)1)), "");

  // The comma operator is not permitted in an integer constant expression
  // (C11 6.6p3), so (void *)(1, 0) is not a null pointer constant either.
  _Static_assert(sizeof(int) != sizeof(*(1 ? ((void *)(1, 0)) : (int *)1)), "");
#else
  static_assert(sizeof(int) == sizeof(*(1 ? ((void *)(0)) : (int *)1)), "");
  // Visual Studio rejects this as "illegal indirection"
  // static_assert(
  //   sizeof(int) == sizeof(*(1 ? ((void *)(i * 0)) : (int *)1)), "");
#endif
}
