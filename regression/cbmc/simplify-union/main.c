#include <assert.h>
#include <stdlib.h>

struct O
{
  char *ptr;
  unsigned len;
};

struct E
{
  int e;
};

union U {
  struct O ok;
  struct E err;
};

struct S
{
  union U u;
  _Bool success;
};

void alloc(struct S *s, unsigned size)
{
  char *p = malloc(sizeof(char) * size);
  if(p != 0)
  {
    s->u.ok = (struct O){p, size};
    s->success = 1;
  }
  else
  {
    s->success = 0;
  }
}

int main()
{
  struct S s;
  alloc(&s, 2);
  if(s.success)
  {
    assert(s.u.ok.len == 2);
    s.u.ok.ptr = "a";
  }
}
