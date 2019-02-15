#include <assert.h>
#include <stdlib.h>

typedef struct A A;
typedef struct B B;
typedef struct C C;
typedef struct D D;

struct A
{
  B *b;
};

struct B
{
  C *c;
};

struct C
{
  D *d;
};

struct D
{
  A *a;
};

void func(A *a)
{
  assert(a != NULL);
  assert(a->b != NULL);
  assert(a->b->c != NULL);
  assert(a->b->c->d != NULL);
  assert(a->b->c->d->a == NULL);
}
