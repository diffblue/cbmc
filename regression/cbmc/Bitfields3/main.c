#include <stdlib.h>
#include <assert.h>

#pragma pack(1)
struct A
{
  unsigned char a;
  unsigned char b : 2;
  unsigned char c : 2;
  unsigned char d;
};

struct B
{
  unsigned char a;
  unsigned char b : 2;
  unsigned char c;
  unsigned char d : 2;
};

struct C
{
  unsigned char a;
  unsigned char b : 4;
  unsigned char c : 4;
  unsigned char d;
};
#pragma pack()

int main(void)
{
  assert(sizeof(struct A) == 3);
  struct A *p = malloc(3);
  assert((unsigned char *)p + 2 == &(p->d));
  p->c = 3;
  if(p->c != 3)
  {
    free(p);
  }
  free(p);

  assert(sizeof(struct B) == 4);
  struct B *pb = malloc(4);
  assert((unsigned char *)pb + 2 == &(pb->c));
  free(pb);

  assert(sizeof(struct C) == 3);
  struct C *pc = malloc(3);
  assert((unsigned char *)pc + 2 == &(pc->d));
  free(pc);

  return 0;
}
