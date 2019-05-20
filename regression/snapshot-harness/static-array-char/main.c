#include <assert.h>

char tmp[12];
char *first;
char *second;
int array_size;

void initialize()
{
  tmp[0] = '1';
  tmp[9] = '0';
  tmp[10] = 'a';
  first = (char *)tmp;
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
  assert(first[0] == '1');
  assert(second[9] == '0');
  return 0;
}
