#include <assert.h>

#ifdef __GNUC__
// GCC runs constructors in ascending priority order; a constructor without a
// priority has priority 65535. Constructors of equal priority are run in the
// order they appear in the program; their names are in the same order here,
// as CBMC orders functions of equal priority by name.
#  define PRIORITY (110)
enum
{
  ENUM_PRIORITY = 120
};

int order[8];
int n;

__attribute__((constructor)) static void a_no_priority(void)
{
  order[n++] = 7;
}
__attribute__((constructor(65535))) static void b_default_priority(void)
{
  order[n++] = 8;
}
__attribute__((constructor(ENUM_PRIORITY))) static void c_enum(void)
{
  order[n++] = 3;
}
__attribute__((constructor(200 + 1))) static void d_sum(void)
{
  order[n++] = 6;
}
__attribute__((constructor(PRIORITY))) static void e_macro(void)
{
  order[n++] = 2;
}
__attribute__((constructor(101))) static void f_literal(void)
{
  order[n++] = 1;
}
__attribute__((constructor(150))) static void g_150(void)
{
  order[n++] = 4;
}
__attribute__((constructor(150))) static void h_150(void)
{
  order[n++] = 5;
}
#endif

int main()
{
#ifdef __GNUC__
  assert(n == 8);
  for(int i = 0; i < 8; ++i)
    assert(order[i] == i + 1);
#endif
  return 0;
}
