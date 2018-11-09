#include <assert.h>

enum E
{
  A = 1,
  B = 2
};

int main()
{
  enum E array[2] = {A, B};
  unsigned *p = array;
  assert(*p == 1);
  return 0;
}
