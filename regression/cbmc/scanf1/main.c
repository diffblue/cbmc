#include <stdio.h>
#include <assert.h>

int main(void)
{
  char c=0;
  int i=0;
  float f=0;
  double d=0;
  long int li=0;
  void *p=0;
  
  scanf("%c", &c);
  scanf("%d", &i);
  scanf("%f", &f);
  scanf("%lf", &d);
  scanf("%ld", &li);
  scanf("%p", &p);

  assert(c==0); // may fail
  assert(i==0); // may fail
  assert(f==0); // may fail
  assert(d==0); // may fail
  assert(li==0); // may fail
  assert(p==0); // may fail

  return 0;
}

