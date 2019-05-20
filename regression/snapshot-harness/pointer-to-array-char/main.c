#include <assert.h>
#include <malloc.h>

char *first;
char *second;
int array_size;

void initialize()
{
  first = malloc(sizeof(char) * 12);
  first = "1234567890a";
  second = first;
  array_size = 11;
}

void checkpoint()
{
}

int main()
{
  initialize();
  checkpoint();

  assert(first == second);
  assert(second[array_size - 1] == 'a');
  return 0;
}
