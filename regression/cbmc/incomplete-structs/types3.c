struct T
{
  int i;
};

struct S
{
  struct T *t;
  struct U *u;
};

int bar(struct S *);

int foo(struct S *s)
{
  return bar(s) + s->t->i;
}
