#include <assert.h>

#ifdef __GNUC__
int x;

static __attribute__((constructor)) void format_init(void);

static __attribute__((constructor))
void format_init(void)
{
  x=42;
  return;
}
#endif

int main()
{
#ifdef __GNUC__
  assert(x==42);
#endif
  return 0;
}
