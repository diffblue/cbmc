// N5008 [dcl.attr.nouniqueaddr]/1, [intro.object]/8: an empty
// [[no_unique_address]] member of an over-aligned class.  GCC and Clang
// (Itanium C++ ABI 2.4 II.3) put it at offset 0, so d follows c at offset
// 1; the member only raises the class's alignment to 8.
#include <cstddef>
extern "C" void __CPROVER_assert(bool, const char *);
struct alignas(8) A8
{
};
struct Q
{
  char c;
  [[no_unique_address]] A8 a;
  char d;
};
int main()
{
  Q q;
  __CPROVER_assert((char *)&q.a == (char *)&q, "at offset 0");
  __CPROVER_assert(offsetof(Q, d) == 1, "d follows c");
  __CPROVER_assert(sizeof(Q) == 8 && alignof(Q) == 8, "size 8");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
