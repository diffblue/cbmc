// Test that value set dereferencing correctly handles the case where a
// pointer to a smaller struct is used to access an object of a larger
// struct type (struct prefix relationship). The removed struct-prefix
// check in dereference_type_compare would have produced a direct cast
// (and a "warning: ignoring" from the solver); now it correctly uses
// byte_extract instead.

#include <assert.h>

struct small
{
  int x;
};

struct big
{
  int x;
  int y;
};

int main()
{
  struct big b = {1, 2};
  void *v = &b;
  struct small *p = (struct small *)v;
  assert(p->x == 1);
  return 0;
}
