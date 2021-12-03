#include <assert.h>
#include <stdlib.h>

int x = 0;
typedef struct stc
{
  int i;
  int j;
} stc;

typedef struct stb
{
  stc *c;
} stb;

typedef struct sta
{
  union {
    stb *b;
    int i;
    int j;
  } u;
} sta;

int nondet_int();

void bar(sta *a)
{
  if(nondet_bool())
    return;
  __CPROVER_havoc_object(a->u.b->c);
  return;
}

void foo(sta *a1, sta *a2)
  __CPROVER_assigns(__CPROVER_POINTER_OBJECT(a1->u.b->c))
{
  bar(a1);
  bar(a2);
  return;
}

sta *allocate_sta()
{
  stc *c = malloc(sizeof(*c));
  stb *b = malloc(sizeof(*b));
  sta *a = malloc(sizeof(*a));
  b->c = c;
  a->u.b = b;
  return a;
}

int main()
{
  sta *a1 = allocate_sta();
  sta *a2 = allocate_sta();
  foo(a1, a2);
  return 0;
}
