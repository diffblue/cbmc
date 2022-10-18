#include <assert.h>

union u_type
{
  int i;
  char ch;
};

int main()
{
  union u_type u;

  u.ch = 2;
  assert(u.ch == 2);
}
