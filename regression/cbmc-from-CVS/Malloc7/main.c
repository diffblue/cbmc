int *global;

void *malloc(unsigned);

struct X
{
  int i;
  struct X *n;
};

int main()
{
  struct X *p;
  struct X x;
  int *q;
  
  p=malloc(sizeof(struct X));
  q=&(p->i);
  
  *q=1;

  // should pass  
  assert(p->i==1);
}
