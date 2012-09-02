#include <assert.h>
#include <string.h> 

int main()
{
  char str[500]="Hello"; 

  assert(strcmp(str, "Hello")==0);
  assert(strncmp(str, "Hello", 5)==0); 
  assert(strcasecmp(str, "HELLO")==0);
  assert(strncasecmp(str, "HELLO", 5)==0);
  assert(strcmp(str, "\xff")<0);
  assert(strncmp("ASDxx", "ASDyy", 3)==0);

  assert(strlen(str)==5);
  assert(strcmp(str, strdup(str))==0);

  return 0;
}
