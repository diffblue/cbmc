#include <assert.h>
#include <stdlib.h>

int x = 0;
typedef struct stc {
  int i;
  int j;
} stc;

typedef struct stb {
  stc *c;
} stb;

typedef struct sta {
  union {
    stb *b;
    int i;
    int j;
  } u;
} sta;

int nondet_int();

void bar(sta *a)
{
  if (nondet_bool()) return;
  __CPROVER_havoc_object(a->u.b->c);
  return;
}

void foo(sta *a) __CPROVER_assigns(__CPROVER_POINTER_OBJECT(a->u.b->c))
{
  bar(a);
  a->u.i = 2;
  return;
}

int main()
{
  stc *c = malloc(sizeof(*c));
  stb *b = malloc(sizeof(*b));
  sta *a = malloc(sizeof(*a));
  b->c = c;
  a->u.b = b;
  foo(a);
  return 0;
}
