#include <assert.h>

union u_type
{
  int i;
  char ch;
};

int main()
{
  union u_type u = {0};

  u.ch = 2;
  assert(u.ch == 2);
}
