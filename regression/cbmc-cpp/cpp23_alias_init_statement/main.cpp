// N5008 [stmt.pre] (grammar: init-statement can be an
// alias-declaration, P2360R0, C++23) + [stmt.if]: `if constexpr
// (using T = ...; condition)` is well-formed.  CBMC's parser rejects
// the alias-declaration init-statement ("parse error before 'using T
// = int'").  libc++ 22 uses this form in __algorithm/for_each.h
// (__for_each's _SpecialAlg dispatch), so EVERY <algorithm>-including
// test breaks against libc++ >= 22 (found running the regression
// suite in an archlinux container, clang 22.1.8).
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int r = 0;
  if constexpr(using T = int; sizeof(T) == 4)
    r = 39;
  if(using T = long; sizeof(T) >= 4)
    r += 1;
  switch(using U = int; sizeof(U))
  {
  case 4:
    r += 2;
    break;
  default:
    break;
  }
  __CPROVER_assert(r == 42, "alias-declaration init-statement");
  return 0;
}
