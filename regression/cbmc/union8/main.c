#include <assert.h>

typedef struct jv_refcnt {
  int count;
} jv_refcnt;

typedef struct {
  union {
    struct jv_refcnt* ptr;
    double number;
  } u;
} jv;

int main(void)
{
  jv_refcnt cnt={.count=1};
  jv container={.u={.ptr=&cnt}};
  struct jv_refcnt *read_ptr=container.u.ptr;
  assert(read_ptr == &cnt);
  assert(read_ptr->count == 1);
}
