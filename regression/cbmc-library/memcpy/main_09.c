#include <assert.h>
#include <string.h>

union _5557197549936569444_union
{
};

struct _5557197549936569444
{
  // _case
  unsigned char _case;
  // cases -- this member makes all the difference
  union _5557197549936569444_union cases;
};

struct _3036371764910125196
{
  // t
  struct _5557197549936569444 t;
  // array
  unsigned char array[8l];
};

void main(void)
{
  struct _3036371764910125196 data = {.t = {._case = 0}, .array = {0}};
  unsigned long int index;
  if(index < 2)
  {
    unsigned char array[4] = {0, 0, 0, 0};
    unsigned long start = index * 4ul;
    unsigned long end = start + 4ul;

    memcpy((unsigned char *)&data.array + start, array, end - start);
    assert(data.t._case == 0);
  }
}
