#include <stdio.h>
#include <assert.h>

int main(void)
{
  char c=0;
  short int si=0;
  int i=0;
  float f=0;
  double d=0;
  long double ld=0;
  long int li=0;
  void *p=0;
  char buffer[10];
  
  __CPROVER_scanf("%c", &c);
  __CPROVER_scanf("%hhd", &si);
  __CPROVER_scanf("%d", &i);
  __CPROVER_scanf("%f", &f);
  __CPROVER_scanf("%lf", &d);
  __CPROVER_scanf("%Lf", &ld);
  __CPROVER_scanf("%li", &li);
  __CPROVER_scanf("%p", &p);
  __CPROVER_scanf("%s", buffer);

  assert(c==0); // may fail
  assert(si==0); // may fail
  assert(i==0); // may fail
  assert(f==0); // may fail
  assert(d==0); // may fail
  assert(li==0); // may fail
  assert(p==0); // may fail
  assert(buffer[0]==0); // may fail

  return 0;
}

