#include <string.h>

void * malloc(unsigned);

int main(int argc, char* argv[]) {
  char * name;

  name = malloc(10);
  __CPROVER_assume(__CPROVER_buffer_size(name) == 20);
  name=strcpy(name, "abcdefghi");
  name=strcpy(name+5-1, "xxxxx");
  assert(__CPROVER_is_zero_string(name));
  
  return 0;
}

