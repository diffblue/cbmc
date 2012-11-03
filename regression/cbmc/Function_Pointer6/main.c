void *malloc(unsigned size);

struct S {
  int (* func) ();
};

int ten()
{
  return 10;
}

int twenty()
{
  return 20;
}

int main(void)
{
  int (*ppp)();
  struct S * ps = (struct S *) malloc(sizeof(struct S));
  int x, y;

  ps->func = x?ten:twenty;

  ppp=ps->func;
  
  y=ps->func();
  
  assert(y==10 || y==20);

  return 0;
}
