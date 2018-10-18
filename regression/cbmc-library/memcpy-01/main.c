#include <assert.h>
#include <string.h>

struct without_ptr
{
  int x;
  int y;
};
struct with_int_ptr
{
  int *i;
  int j;
};
struct with_struct_ptr
{
  struct without_ptr *s;
  int t;
};

int main(int argc, char **argv)
{
  struct without_ptr w;
  w.x = 42;
  w.y = 43;

  struct without_ptr v;
  memcpy(&v, &w, sizeof(struct without_ptr));
  assert(v.x == 42);
  assert(v.y == 43);

  struct with_int_ptr k;
  k.i = (int *)44;
  k.j = 45;

  struct with_int_ptr m;
  memcpy(&m, &k, sizeof(struct with_int_ptr));
  assert(m.i == (int *)44);
  assert(m.j == 45);

  struct with_struct_ptr p;
  p.s = &w;
  p.t = 46;

  struct with_struct_ptr q;
  memcpy(&q, &p, sizeof(struct with_struct_ptr));
  assert(q.s->x == 42);
  assert(q.s->y == 43);
  assert(q.t == 46);

  return 0;
}
