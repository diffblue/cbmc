// #include <string.h> intentionally omitted

struct c
{
  int d;
};

struct e
{
  struct c *f;
};

struct g
{
  const char *b;
};

int main()
{
  unsigned long nondet;

  struct g *r = (struct g *)nondet;
  r->b = "";

  struct e *x = (struct e *)nondet;
  int *d = &x->f->d;

  memcpy(d + 2, 0, 0);
}
