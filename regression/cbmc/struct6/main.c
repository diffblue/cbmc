void *malloc(unsigned);

struct S
{
  int x;
  char a[];
};

void *malloc(int);

int main()
{
  struct S *p=malloc(sizeof(struct S)+10);
  
  p->x=1;
  p->a[0]=3;
  p->a[9]=3;
}
