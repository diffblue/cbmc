#include <assert.h>
#include <string.h> 
void free(void *);

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
  char * str_cpy=strdup(str);
  assert(strcmp(str, str_cpy)==0);
  free(str_cpy);

  return 0;
}
