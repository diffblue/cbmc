#  include <assert.h>

#if defined(__GLIBC__) &&                                                      \
  (__GLIBC__ > 2 || (__GLIBC__ == 2 && __GLIBC_MINOR__ >= 25))
#  include <sys/random.h>

int main()
{
  char zero_bytes[6] = {0};
  ssize_t res = getrandom(zero_bytes, 5, 0);
  assert(res <= 5);
  assert(zero_bytes[5] == 0);
  return 0;
}
#else
int main()
{
}
#endif
