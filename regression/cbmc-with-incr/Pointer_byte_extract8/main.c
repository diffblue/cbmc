#include <stdlib.h>

typedef union
{
  int a;
  int b;
} Union;

typedef struct
{
  int Count;
  Union List[1];
} __attribute__((packed)) Struct3;

int main()
{
  Struct3 *p = malloc (sizeof (int) + 2 * sizeof(Union));
  p->Count = 3;
  int po=0;

  // this should be fine
  p->List[0].a = 555;

  __CPROVER_assert(p->List[0].b==555, "p->List[0].b==555");
  __CPROVER_assert(p->List[0].a==555, "p->List[0].a==555");

  // this should be fine
  p->List[1].b = 999;

  __CPROVER_assert(p->List[1].b==999, "p->List[1].b==999");
  __CPROVER_assert(p->List[1].a==999, "p->List[1].a==999");

  // this is out-of-bounds
  p->List[2].a = 0;

  return 0;
}
