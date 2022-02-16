#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

struct pair
{
  uint8_t *buf;
  size_t size;
};

struct pair_of_pairs
{
  struct pair *p;
};

void f1(struct pair *p) __CPROVER_assigns(*(p->buf))
{
  p->buf[0] = 0;
}

void f2(struct pair_of_pairs *pp) __CPROVER_assigns(*(pp->p->buf))
{
  pp->p->buf[0] = 0;
}

int main()
{
  struct pair *p = malloc(sizeof(*p));
  if(p)
    p->buf = malloc(100 * sizeof(uint8_t));
  f1(p);

  struct pair_of_pairs *pp = malloc(sizeof(*pp));
  if(pp)
  {
    pp->p = malloc(sizeof(*(pp->p)));
    if(pp->p)
      pp->p->buf = malloc(100 * sizeof(uint8_t));
  }
  f2(pp);

  return 0;
}
