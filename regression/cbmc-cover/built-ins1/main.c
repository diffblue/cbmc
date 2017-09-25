#include <string.h>

int main()
{
  char a[10];
  __CPROVER_input("a[3]", a[3]);

  int len=strlen(a);

  if(len==3)
  {
    return 0;
  }
  else if(len==4)
  {
    return -1;
  }

  return 1;
}
