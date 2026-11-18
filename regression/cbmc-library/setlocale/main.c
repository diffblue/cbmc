#include <assert.h>
#include <locale.h>
#include <stddef.h>

int main(void)
{
  // C11 7.11.1.1p6: setlocale may return NULL on failure.
  char *r = setlocale(LC_ALL, "C");
  // The result is nondeterministic: may be NULL (failure) or non-NULL.
  // Assert it's always non-NULL: this must FAIL, proving the NULL path
  // is reachable.
  assert(r != NULL);

  return 0;
}
