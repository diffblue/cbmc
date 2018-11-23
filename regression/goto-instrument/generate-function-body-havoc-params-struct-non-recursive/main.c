#include <assert.h>
#include <stdlib.h>

typedef struct st
{
  int data;
} st_t;

void func(st_t *p);

void main()
{
  st_t st;
  st.data = 0;

  func(&st);

  assert(st.data == 0);
}
