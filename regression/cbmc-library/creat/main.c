#include <fcntl.h>

#ifdef _WIN32
#  define MODE_T int
#else
#  define MODE_T mode_t
#endif

int main()
{
  char *unint_path;
  MODE_T mode;
  int fd = creat(unint_path, mode);
  return 0;
}
