#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

struct pair
{
  uint8_t *buf;
  size_t size;
};

void f1(struct pair *p) __CPROVER_assigns(*(p->buf))
  __CPROVER_ensures(p->buf[0] == 0)
{
  p->buf[0] = 0;
}

int main()
{
  struct pair *p = nondet_bool() ? malloc(sizeof(*p)) : NULL;
  f1(p);
  // clang-format off
  assert(p != NULL ==> p->buf[0] == 0);
  // clang-format on
  return 0;
}
