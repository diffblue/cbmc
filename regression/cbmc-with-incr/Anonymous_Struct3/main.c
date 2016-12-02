#include <assert.h>

typedef union my_U {
  struct my_S {
    unsigned      : 1;
    unsigned f1   : 1;
  };
  char raw;
} fields_t;

fields_t x;

int main()
{
  x.f1 = 1;
  assert(x.raw==2);
}
