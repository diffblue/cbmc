#include <functional>
extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  int x;
  int y;
};
int S::*global = &S::y;
int main()
{
  S s{3, 4};
  // [func.require]/1.4-1.6: INVOKE of a pointer to data member
  __CPROVER_assert(std::invoke(&S::y, s) == 4, "invoke");
  __CPROVER_assert(std::mem_fn(&S::x)(s) == 3, "mem_fn");
  __CPROVER_assert(s.*global == 4, "namespace-scope pointer to member");
  __CPROVER_assert(std::invoke(&S::x, &s) == 4, "WRONG (must FAIL)");
}
