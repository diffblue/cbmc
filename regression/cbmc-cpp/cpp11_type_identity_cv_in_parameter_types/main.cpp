extern "C" void __CPROVER_assert(bool, const char *);
#include <type_traits>
struct S { int f(int) const; int g(int); };
int main()
{
  __CPROVER_assert(!std::is_same<void (*)(const int *), void (*)(int *)>::value, "cv inside a parameter pointee distinguishes function pointer types");
  __CPROVER_assert(!std::is_same<const int *, int *>::value, "cv inside a pointee");
  __CPROVER_assert(!std::is_same<int (S::*)(int) const, int (S::*)(int)>::value, "cv-qualified pmf distinct");
  __CPROVER_assert(!std::is_same<decltype(&S::f), decltype(&S::g)>::value, "decltype(&S::f) const vs non-const");
  return 0;
}
