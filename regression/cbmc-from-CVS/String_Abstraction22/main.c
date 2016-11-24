#include <string.h>

int main()
{
  char a[100], *p;
  _Bool x;

  p=x ? strcpy(a, "asd") : strcpy(a, "abc");
  assert(p==a);
  assert(strlen(a)==3);
  assert(strlen(p)==3);
}
