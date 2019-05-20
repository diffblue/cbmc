#include <assert.h>

char *first = "12345678901";
char *second;
int string_size;
const char *prefix;
int prefix_size;

void initialize()
{
  second = first;
  string_size = 11;
}

void checkpoint()
{
}

int main()
{
  initialize();
  checkpoint();

  assert(first == second);
  if(prefix_size > 0)
    assert(second[prefix_size - 1] != 'a');

  if(string_size < prefix_size)
  {
    return 0;
  }

  for(int ix = 0; ix < prefix_size; ++ix)
  {
    if(second[ix] != prefix[ix])
    {
      return 0;
    }
  }
  return 1;
}
