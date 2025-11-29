// _Generic must distinguish pointer-to-const from pointer-to-non-const
// (C11 6.5.1.1: matching is by compatible type after lvalue conversion;
// top-level qualifiers are dropped, but pointee qualifiers are not).
// Plain irept == ignored the qualifier "comments", so `int *` wrongly
// matched `const int *`.  This is the basis of the Linux kernel's
// container_of_const()/inet_sk() macro.
#include <stddef.h>

#define container_of(p, type, member)                                          \
  ((type *)((char *)(p)-offsetof(type, member)))
#define container_of_const(p, type, member)                                    \
  _Generic(p, \
    const __typeof__(*(p)) *: ((const type *)container_of(p, type, member)), \
    default: ((type *)container_of(p, type, member)))

struct sock
{
  int x;
};
struct inet_sock
{
  struct sock sk;
  int csum;
};

int main(void)
{
  struct sock *p = 0;
  int r = _Generic(p, const struct sock * : 1, default : 2);
  __CPROVER_assert(r == 2, "non-const ptr -> default");

  const struct sock *cp = 0;
  int r2 = _Generic(cp, const struct sock * : 1, default : 2);
  __CPROVER_assert(r2 == 1, "const ptr -> const branch");

  // exact non-const branch must win over a const branch
  int r3 = _Generic(p, struct sock * : 3, const struct sock * : 1, default : 2);
  __CPROVER_assert(r3 == 3, "exact non-const branch");

  // container_of_const on a non-const pointer yields a *modifiable* lvalue
  struct inet_sock is;
  is.csum = 0;
  container_of_const(&is.sk, struct inet_sock, sk)->csum++; // must compile
  __CPROVER_assert(is.csum == 1, "container_of_const writable");

  // C11 lvalue conversion: an array controlling expression decays to a
  // pointer (kernel ATTRIBUTE_GROUPS: _Generic(attrs[], struct X **: ...)).
  static struct sock *arr[2] = {0, 0};
  int r4 = _Generic(arr, struct sock * * : 5, default : 6);
  __CPROVER_assert(r4 == 5, "array decays to pointer");

  return 0;
}
