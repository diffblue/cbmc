#include <assert.h>
#include <stdlib.h>
#include <string.h>

int main()
{
  int size = 4;
  char *str = malloc(sizeof(char) * size);
  char nondet_char;
  __CPROVER_assume(nondet_char != '\0');
  str[0] = nondet_char;
  char nondet_char2;
  __CPROVER_assume(str[1] != '\0');
  //  str[1] = nondet_char2;
  str[2] = 'z';
  str[3] = '\0';
  char *result = strchr(str, 'z');
  assert(result);
  __CPROVER_assert(0, "unreachable");
  // assert(result == str+1);
  //  assert(result == str);

  return 0;
}
