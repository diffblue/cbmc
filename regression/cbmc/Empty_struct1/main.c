#include <assert.h>

struct empty
{
};

int main()
{
  struct empty e1, e2, e3;
  _Bool b, c=b;
  e1=e2;
  if(b)
    e3=e2;

  assert(b==c);
}
