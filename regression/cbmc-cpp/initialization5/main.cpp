#include <cassert>
int a[(__CPROVER_size_t)1 << (sizeof(__CPROVER_size_t) * 8 - 2)];

struct A
{
  int i[(__CPROVER_size_t)1 << (sizeof(__CPROVER_size_t) * 8 - 2)];
};

A o;

int main()
{
  unsigned x;
  assert(o.i[x] == 0);
  assert(a[x] == 0);
}
