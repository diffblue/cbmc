#include <stdlib.h>

#ifdef _WIN32
void *alloca(size_t alloca_size);
#endif

int main()
{
  int *p = alloca(sizeof(int));
  *p = 42;
  free(p);
  (void)alloca(sizeof(int)); // useless, but result still needs to be released
}
