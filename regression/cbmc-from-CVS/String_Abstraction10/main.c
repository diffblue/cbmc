#include <string.h>

char a [10][100];

struct S
{
  char x[100];
  char *p;
} s;

int main()
{
  strcpy(a[0], "asd");
  assert(strlen(a[0])==3);
  
  strcpy(s.x, "asdasd");
  assert(strlen(s.x)==6);
  
  s.p=s.x;
  assert(strlen(s.p)==6);
}
