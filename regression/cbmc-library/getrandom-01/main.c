#ifdef __linux__
#  include <sys/random.h>

#  include <assert.h>

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
