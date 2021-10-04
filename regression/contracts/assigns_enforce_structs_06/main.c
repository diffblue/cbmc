#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

struct pair
{
  uint8_t *buf;
  size_t size;
};

void f1(struct pair *p) __CPROVER_assigns(__CPROVER_POINTER_OBJECT(p->buf))
{
  p->buf[0] = 0;
  p->buf[1] = 1;
  p->buf[2] = 2;
  p->size = 4;
}

void f2(struct pair *p) __CPROVER_assigns(p->size)
{
  p->buf[0] = 0;
  p->size = 0;
}

void f3(struct pair *p) __CPROVER_assigns(*p)
{
  p->buf = NULL;
  p->size = 0;
}

int main()
{
  struct pair *p = malloc(sizeof(*p));
  p->size = 3;
  p->buf = malloc(p->size);
  f1(p);
  assert(p->buf[0] == 0);
  assert(p->buf[1] == 1);
  assert(p->buf[2] == 2);
  f2(p);
  assert(p->size == 0);
  f3(p);
  assert(p->buf == NULL);
  assert(p->size == 0);
  return 0;
}
