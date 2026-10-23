#include <string.h>

int main()
{
  char a[100], *p;
  _Bool x = __VERIFIER_nondet__Bool();

  p = x ? strcpy(a, "asd") : strcpy(a, "abc");
  assert(p == a);
  assert(strlen(a) == 3);
  assert(strlen(p) == 3);
}
