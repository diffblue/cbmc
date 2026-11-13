// C11 6.5.1.1: generic selection matches by type compatibility (6.2.7) after
// lvalue conversion of the controlling expression.
#include <stddef.h>

enum E
{
  A
};
enum N
{
  M = -1
};
typedef enum E enumE;
typedef enum N enumN;

_Noreturn void die(void);
__attribute__((noreturn)) void die2(void);
int g(const int);
int fixed(int);
int variadic(int, ...);

void f(int n)
{
  // lvalue conversion removes _Atomic, too (6.3.2.1p2)
  _Atomic int a = 0;
  _Static_assert(_Generic(a, int: 1, default: 2) == 1, "atomic");
  int *_Atomic ap = 0;
  _Static_assert(_Generic(ap, int *: 1, default: 2) == 1, "atomic ptr");

  // _Noreturn is a function specifier, not part of the type
  _Static_assert(_Generic(die, void (*)(void): 1, default: 2) == 1, "nr");
  _Static_assert(_Generic(die2, void (*)(void): 1, default: 2) == 1, "nr2");

  // parameter types are compared unqualified (6.7.6.3p15)
  _Static_assert(_Generic(g, int (*)(int): 1, default: 2) == 1, "param");

  // a prototype with ellipsis is not compatible with one without
  _Static_assert(
    _Generic(fixed, int (*)(int, ...): 1, default: 2) == 2, "ellipsis");
  _Static_assert(
    _Generic(variadic, int (*)(int): 1, default: 2) == 2, "ellipsis2");
  _Static_assert(
    _Generic(fixed, int (*)(int): 1, int (*)(int, ...): 2) == 1, "both");

  // variable length arrays are compatible with any size (6.7.6.2p6)
  int vla[n];
  _Static_assert(_Generic(&vla, int(*)[5]: 1, default: 2) == 1, "vla");
  _Static_assert(__builtin_types_compatible_p(int[n], int[5]), "vla");

  // arrays of different constant sizes are not compatible
  int a5[5];
  _Static_assert(_Generic(&a5, int(*)[10]: 1, default: 2) == 2, "size");
  _Static_assert(_Generic(&a5, int(*)[2 + 3]: 1, default: 2) == 1, "fold");

  // in C, wchar_t is a typedef for an integer type
  _Static_assert(_Generic(L'a', wchar_t: 1, default: 2) == 1, "wchar_t");

  // an enum is compatible with its underlying type, as chosen by GCC
  unsigned u = 0;
  int i = 0;
  enumE e = A;
  _Static_assert(_Generic(e, unsigned: 1, default: 2) == 1, "enum");
  _Static_assert(_Generic(u, enumE: 1, default: 2) == 1, "enum");
  _Static_assert(_Generic(e, int: 1, default: 2) == 2, "enum");
  _Static_assert(_Generic(i, enumN: 1, default: 2) == 1, "enum");
}

int main(void)
{
  return 0;
}
