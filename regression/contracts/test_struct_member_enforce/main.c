#include <assert.h>

struct string
{
  int len;
  char *str;
};

// clang-format off
int foo(struct string *x)
  __CPROVER_assigns(x->str[x->len-1])
  __CPROVER_requires(
    x->len == 128 &&
    __CPROVER_is_fresh(x->str, x->len * sizeof(char)))
  __CPROVER_ensures(
    __CPROVER_return_value == 128 &&
    x->str[x->len - 1] == '\0')
// clang-format on
{
  x->str[x->len - 1] = '\0';
  return x->len;
}

int main()
{
  struct string x;
  int rval = foo(&x);
  assert(rval == 128);
  return 0;
}
