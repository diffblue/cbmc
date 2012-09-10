#include <assert.h>

int main()
{
  int some_int=20;
  int *p;
  p=(int []){ 1, 2, 3, some_int };
  
  assert(p[0]==1);
  assert(p[1]==2);
  assert(p[2]==3);
  assert(p[3]==20);
  
  struct S { int x, y; } *q;
  
  q=&(struct S){ .x=1 };
  
  assert(q->x==1);
  assert(q->y==0);
  
  const char *sptr="asd";
  assert(sptr[0]=='a');
  assert(sptr[1]=='s');
  assert(sptr[2]=='d');
  assert(sptr[3]==0);
}
