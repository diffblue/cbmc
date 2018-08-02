#include <assert.h>

int g, k;

// See https://gcc.gnu.org/onlinedocs/gcc/Conditionals.html
int main()
{
  int r1, r2;

  r1= (g++) ? : 2;

  assert(r1==2);
  assert(g==1);

  r2= (g++) ? : (k++);

  assert(r2==1);
  assert(g==2);
  assert(k==0);

  int in_decl = g++ ?: 0;
  assert(in_decl == 2);
  assert(g == 3);

  return 0;
}
