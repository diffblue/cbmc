#include <cassert>

int main()
{
  int x = 7;
  int *q = &x;

  // auto with a pointer declarator: per [dcl.type.auto.deduct] the
  // declarator's '*' is part of the deduction pattern, so `auto`
  // deduces to int (not int*) and p has type int*.
  auto *p = &x;
  *p = 42;
  assert(x == 42);

  // const-qualified pointee
  const auto *cp = q;
  assert(*cp == 42);

  // pointer-to-pointer declarator: auto deduces to int, pp is int**
  int *r = &x;
  auto **pp = &r;
  assert(**pp == 42);

  // auto& bound to a pointer lvalue: the reference is NOT a pointer
  // declarator, so auto absorbs the full type int* (ar has type int*&)
  auto &ar = q;
  assert(*ar == 42);

  return 0;
}
