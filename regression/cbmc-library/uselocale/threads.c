#include <assert.h>
#include <locale.h>
#include <pthread.h>

static char dummy1, dummy2;

void *child(void *arg)
{
  (void)arg;
  assert(uselocale((locale_t)0) == LC_GLOBAL_LOCALE);
  uselocale((locale_t)&dummy2);
  assert(uselocale((locale_t)0) == (locale_t)&dummy2);
  return 0;
}

int main()
{
  uselocale((locale_t)&dummy1);
  pthread_t t;
  pthread_create(&t, 0, child, 0);
  pthread_join(t, 0);
  assert(uselocale((locale_t)0) == (locale_t)&dummy1);
  return 0;
}
