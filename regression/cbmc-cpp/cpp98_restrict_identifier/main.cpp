extern "C" void __CPROVER_assert(bool, const char *);

// `restrict` is a C11 keyword (C11 6.4.1) but NOT reserved in C++
// ([lex.key]); it is a valid identifier.  CBMC's own miniBDD declares
// `mini_bddt restrict(const mini_bddt &, ...)`.  The shared ansi-c
// scanner treated it as TOK_RESTRICT in C++ mode too, breaking the
// parse of 5 dog-food files -- fixed 2026-07-21 (conditional_keyword
// gate, like _Bool).  __restrict/__restrict__ remain keywords in both
// languages (GNU extension), and C-mode `restrict` still parses.
// g++/clang++ accept and verify at runtime.
int restrict(int x)
{
  return x + 1;
}

int main()
{
  __CPROVER_assert(restrict(41) == 42, "restrict is an identifier in C++");
  return 0;
}
