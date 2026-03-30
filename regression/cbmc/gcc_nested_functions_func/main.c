// __func__ in the enclosing function should still resolve to the
// enclosing function's name AFTER a nested function definition has
// been parsed: the parser must restore the outer function's
// source_location.function rather than clearing it.
//
// Also exercises that a global symbol with the same base name as the
// nested function survives in parser-side lookups for code following
// main(): caller() still calls the global helper, not the nested one.
#include <string.h>

int helper(int x)
{
  return x * 100;
}

int main()
{
  int outer = 10;

  // Nested function with the same base name as the global `helper`.
  int helper(int x)
  {
    return x + outer;
  }

  // Inside main, `helper` resolves to the nested one.
  __CPROVER_assert(helper(5) == 15, "nested helper from main");

  // After parsing the nested function body, parsing continues inside
  // main(). The parser-wide source_location.function should still be
  // "main" so __func__ expands to "main".
  __CPROVER_assert(strcmp(__func__, "main") == 0, "outer __func__ is main");

  return 0;
}

// caller is parsed after main has finished. The global `helper` must
// still be resolvable: the nested-function machinery must not have
// erased the parser's root-scope mapping for the global symbol.
int caller(void)
{
  return helper(5);
}
