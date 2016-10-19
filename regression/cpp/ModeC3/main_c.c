#include <assert.h>

int some_function(int);

int main()
{
  int return_value=some_function(2);
  assert(return_value==3);
}
