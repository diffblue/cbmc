#include <assert.h>

struct famt
{
  char x;
  char vl[];
};

extern struct famt vls;
struct famt vls = {'a', {1, 2, 3, 4}};

int main()
{
  assert(vls.vl[3] == 4);
  return 0;
}
