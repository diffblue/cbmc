#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

struct test
{
  uint8_t buf[8];
};

void f1(struct test *p) __CPROVER_assigns(p->buf)
  __CPROVER_ensures((p == NULL) || p->buf[0] == 0)
{
  if(p != NULL)
    p->buf[0] = 0;
}

int main()
{
  struct test *p = malloc(sizeof(*p));
  uint8_t buf_1 = (p == NULL) ? 0 : p->buf[1];
  f1(p);
  assert(p == NULL || p->buf[0] == 0);
  assert(p == NULL || p->buf[1] == buf_1);
}
