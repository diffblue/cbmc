#include <stdarg.h>

int vsn(char *buf, const char *fmt, ...)
{
  va_list ap;
  va_start(ap, fmt);
  int r = __builtin_vsnprintf(buf, 4, fmt, ap);
  va_end(ap);
  return r;
}

int main()
{
  char buf[4];
  vsn(buf, "%d", 1);
  // declared with void * streams, while the models use FILE *
  __builtin_fputs("x", (void *)0);
  __builtin_fwrite(buf, 1, 1, (void *)0);
  // GCC's __builtin_setjmp is not the C library's setjmp
  void *jb[5];
  __builtin_setjmp(jb);
  return 0;
}
