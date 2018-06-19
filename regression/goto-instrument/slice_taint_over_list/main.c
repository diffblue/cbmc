// This is a benchmark for the full-slicer
// This is a simplified version of end-to-end regression test
// 'taint_over_list' of the security-scanner.

#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

extern void *CProver_nondetWithNull();

struct object
{
  bool Tainted_data;
};

struct java_array
{
  struct object super;
  void **data;
  int length;
};

struct ArrayList
{
  struct java_array *data;
  int last;
};

struct A
{
  struct object super;
};

void ArrayList_init(struct ArrayList *this)
{
  this->data = CProver_nondetWithNull();
  this->last = 0;
}

void ArrayList_add(struct ArrayList *this, struct object *o)
{
  // Next 2 lines are wrongly sliced away!
  this->data->data[this->last] = o;
  this->last += 1;
}

struct object *ArrayList_get(struct ArrayList *this, int idx)
{
  return this->data->data[idx];
}

int main()
{
  struct ArrayList *L;
  struct A *tmp1;
  struct object *tmp2, *tmp3;
  L = CProver_nondetWithNull();
  ArrayList_init(L);
  tmp1 = (struct A *)malloc(sizeof(struct A));
  ArrayList_add(L, (struct object *)&tmp1->super);
  tmp2 = ArrayList_get(L, 0);

  // The next line is wrongly sliced away!
  ((struct A *)tmp2)->super.Tainted_data = true;

  tmp3 = ArrayList_get(L, 0);
  if(((struct A *)tmp3)->super.Tainted_data)
    assert(false);
  return 0;
}
