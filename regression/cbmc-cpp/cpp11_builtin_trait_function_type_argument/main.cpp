// N5008 [dcl.name]/1: a type-trait argument is a type-id, which may name a
// function type.  `__is_function(void())' and `__is_same(void(), void())'
// were parse errors.  (gcc 13 has no __is_function built-in; clang 18 accepts
// this program.)
extern "C" void __CPROVER_assert(bool, const char *);
static_assert(__is_function(void()), "unary");
static_assert(__is_function(int(char, ...)), "variadic function type");
static_assert(!__is_function(void (*)()), "pointer");
static_assert(__is_same(void(), void()), "binary");
static_assert(!__is_same(void(int), void()), "binary differs");
static_assert(__is_trivially_constructible(int, int), "variadic trait");

int main()
{
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
