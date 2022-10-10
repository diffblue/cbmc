struct S
{
  struct T *t;
  struct U *u;
};

struct U
{
  struct S *s;
  int j;
};

int bar(struct S *s)
{
  return s->u->j;
}
