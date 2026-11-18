// cl does not declare the GCC builtins
#ifndef __GNUC__
void *__builtin_memcpy(void *, const void *, __CPROVER_size_t);
void *__builtin_memmove(void *, const void *, __CPROVER_size_t);
#endif

int main()
{
  char buffer[4];
  char *null = 0;
  // a non-zero length still requires valid regions
  __builtin_memcpy(buffer, null, 1);
  __builtin_memcpy(null, buffer, 1);
  __builtin_memmove(buffer, null, 1);
  __builtin_memmove(null, buffer, 1);
  return 0;
}
