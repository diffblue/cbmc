#include <assert.h>
#include <stdlib.h>

struct slot
{
  int id;
  unsigned char data[4];
};

struct ring
{
  struct slot slots[3];
  unsigned count;
};

struct with_array
{
  int x;
  int a[8];
} g;

int main()
{
  unsigned i, j, k;
  __CPROVER_assume(i < 3 && j < 4 && k < 4 && k != j);

  // update of an array member of an element of an array of structs
  struct slot s[3];
  unsigned char before = s[i].data[k];
  s[i].data[j] = 7;
  s[i].id = 5;
  assert(s[i].data[j] == 7);
  assert(s[i].data[k] == before);
  assert(s[i].id == 5);

  // a struct with an array member as a whole
  struct slot t = s[i];
  assert(t.data[j] == 7 && t.id == 5);
  struct ring r;
  r.slots[i] = t;
  r.slots[i].data[k] = 9;
  assert(r.slots[i].data[j] == 7 && r.slots[i].data[k] == 9);

  struct slot u;
  struct ring q;
  q.slots[i] = u;
  assert(q.slots[i].data[j] == u.data[j]);
  assert(q.slots[i].data[k] == u.data[k] && q.slots[i].id == u.id);

  // an array member of a global struct
  unsigned m;
  __CPROVER_assume(m == j);
  g.a[j] = 5;
  assert(g.a[m] == 5);

  // the same on the heap
  struct ring *h = malloc(sizeof(struct ring));
  if(h)
  {
    h->slots[i].id = 3;
    h->slots[i].data[j] = 1;
    assert(h->slots[i].id == 3 && h->slots[i].data[j] == 1);
  }

  assert(0);
  return 0;
}
