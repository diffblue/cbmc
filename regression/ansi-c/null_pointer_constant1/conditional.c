// The type of a conditional expression with a `void *` operand depends on
// whether that operand is a null pointer constant, i.e. an integer constant
// expression with value 0 cast to `void *` (C11 6.3.2.3p3, 6.5.15p6, 6.6p6).
// If it is, the result has the type of the other operand (here `int *`);
// otherwise it is `void *`. NPC(e) is 1 exactly when (void *)(e) is a null
// pointer constant.
#define NPC(e) (sizeof(int) == sizeof(*(1 ? ((void *)(e)) : (int *)1)))
#define NPC_SWAPPED(e) (sizeof(int) == sizeof(*(1 ? (int *)1 : ((void *)(e)))))

// Linux kernel, include/linux/compiler.h (before and since 6.12)
#define __is_constexpr(x)                                                      \
  (sizeof(int) == sizeof(*(8 ? ((void *)((long)(x) * 0l)) : (int *)8)))
#define __is_const_zero(x)                                                     \
  _Generic(0 ? (void *)(long)(x) : (char *)0, char *: 1, void *: 0)
#define is_const(x) __is_const_zero(0 * (x))

struct S
{
  int a;
};
enum
{
  ZERO
};
int f(void);
int g;

int main(int argc, char *argv[])
{
  int x = argc;
  int *p = &x;
  double d = 0.0;
  (void)p;
  (void)d;

  // integer constant expressions with value 0
  _Static_assert(NPC(0), "");
  _Static_assert(NPC(0l), "");
  _Static_assert(NPC((long)0), "");
  _Static_assert(NPC(5 * 0), "");
  _Static_assert(NPC(1 - 1), "");
  _Static_assert(NPC(2 / 2 - 1), "");
  _Static_assert(NPC(0 << 3), "");
  _Static_assert(NPC(1 ? 0 : 1), "");
  _Static_assert(NPC('\0'), "");
  _Static_assert(NPC(ZERO), "");
  _Static_assert(NPC(sizeof(x) * 0), "");
  _Static_assert(NPC(sizeof(f()) * 0), "");
  _Static_assert(NPC(sizeof(*p) * 0), "");
  _Static_assert(NPC(_Alignof(int) * 0), "");
  _Static_assert(NPC(__builtin_offsetof(struct S, a)), "");
  _Static_assert(NPC((long)0.0), "");
  _Static_assert(NPC((int)0.5), "");
  _Static_assert(NPC_SWAPPED(5 * 0), "");

  // expressions that simplify to 0 but are not integer constant expressions
  _Static_assert(!NPC((long)x * 0l), "");
  _Static_assert(!NPC(0 * x), "");
  _Static_assert(!NPC(x - x), "");
  _Static_assert(!NPC(g * 0), "");
  _Static_assert(!NPC(x ? 0 : 0), "");
  _Static_assert(!NPC(0 ? x : 0), "");
  _Static_assert(!NPC(0 && x), "");
  _Static_assert(!NPC((long)*p * 0), "");
  _Static_assert(!NPC((long)*(int *)0 * 0), "");
  _Static_assert(!NPC((long)f() * 0), "");
  _Static_assert(!NPC(x++ * 0), "");
  _Static_assert(!NPC((long)&x - (long)&x), "");
  _Static_assert(!NPC((long)&((struct S *)0)->a), "");
  _Static_assert(!NPC((1, 0)), "");
  _Static_assert(!NPC((long)(1, 0) * 0l), "");
  _Static_assert(!NPC((long)"abc" * 0), "");
  _Static_assert(!NPC((long)__func__ * 0), "");
  _Static_assert(!NPC((long)(0.0 * 1.0)), "");
  _Static_assert(!NPC((long)(double)0), "");
  _Static_assert(!NPC((int *)0), "");
  _Static_assert(!NPC((void *)0), "");
  _Static_assert(!NPC_SWAPPED((long)x * 0l), "");

  // only a cast to unqualified `void *` makes a null pointer constant
  _Static_assert(
    _Generic(1 ? (const void *)0 : (int *)1, int *: 0, default: 1), "");
  _Static_assert(
    _Generic(1 ? (void *)0 : (const int *)1, const int *: 1, default: 0), "");

  // the kernel idioms
  _Static_assert(__is_constexpr(5), "");
  _Static_assert(!__is_constexpr(x), "");
  _Static_assert(is_const(5), "");
  _Static_assert(!is_const(x), "");

  return 0;
}
