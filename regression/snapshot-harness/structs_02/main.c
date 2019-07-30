#include <assert.h>

struct S
{
  int c1;
  int c2;
} st;

int *p;

void initialize()
{
  st.c1 = 1;
  st.c2 = 3;
  p = &(st.c2);
}

void checkpoint()
{
}

int foo()
{
  initialize();
  checkpoint();

  assert(st.c1 + 2 == st.c2);
  assert(st.c1 + 2 == *p);
  assert(*p == st.c2);
  *p = st.c2 + 1;
  assert(*p == st.c2);

  return 0;
}

int main()
{
  foo();

  return 0;
}
