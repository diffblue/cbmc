#include <assert.h>
#include <locale.h>

int main()
{
  localeconv();
  assert(0);
  return 0;
}
