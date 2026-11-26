// Clang's __builtin_invoke(f, t1, ..., tN) is INVOKE of N5008
// [func.require]/1: a pointer to member applied to an object, a
// reference_wrapper or a pointer (/1.1-1.6), any other callable called
// (/1.7).  Xcode 26's libc++ implements std::invoke, std::invoke_result and
// std::is_invocable with it.  (Clang 21+; checked natively with std::invoke.)
#include <functional>
#ifndef __CPROVER__
#  define __builtin_invoke std::invoke
#endif
extern "C" void __CPROVER_assert(bool, const char *);

struct S
{
  int v = 4;
  int get(int k) const
  {
    return v + k;
  }
};
struct D : S
{
};
int add(int a, int b)
{
  return a + b;
}

int main()
{
  S s;
  D d;
  S *p = &s;
  auto twice = [](int x) { return x * 2; };
  __CPROVER_assert(__builtin_invoke(add, 1, 2) == 3, "function");
  __CPROVER_assert(__builtin_invoke(twice, 5) == 10, "lambda");
  __CPROVER_assert(__builtin_invoke(&S::get, s, 1) == 5, "member, object");
  __CPROVER_assert(__builtin_invoke(&S::get, d, 2) == 6, "member, derived");
  __CPROVER_assert(__builtin_invoke(&S::get, p, 3) == 7, "member, pointer");
  __CPROVER_assert(
    __builtin_invoke(&S::get, std::ref(s), 4) == 8,
    "member, reference_wrapper");
  __CPROVER_assert(__builtin_invoke(&S::v, s) == 4, "data member");
  __CPROVER_assert(__builtin_invoke(&S::v, p) == 4, "data member, pointer");
  __builtin_invoke(&S::v, s) = 9;
  __CPROVER_assert(s.v == 9, "data member is an lvalue");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
