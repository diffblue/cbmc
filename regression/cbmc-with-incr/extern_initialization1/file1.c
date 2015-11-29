#include <assert.h>

extern int some_int;

int main()
{
  // fails
  assert(some_int==0);
}
