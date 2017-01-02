#include <stdlib.h>

struct A
{
  int x;
  int y;
};

int main()
{
  struct A *p=malloc(sizeof(int));
  p->x=0; // OK
  p->y=0; // out of bounds

  struct A o=*p; // out of bounds

  int *p2=malloc(sizeof(int));
  p2[0]=0; // OK
  p2[1]=0; // out of bounds

  ++p2;
  p2[0]=0; // out of bounds

  return 0;
}
