#include <string.h>

int main()
{
  char a[100], b[100], *p;
  
  strcpy(a, "asd");
  assert(strlen(a)==3);
  
  a[2]=0;
  assert(strlen(a)==2);
  
  p=strcpy(b, a);
  assert(p==b);
  assert(strlen(b)==2);  
  assert(strlen(p)==2);
}
