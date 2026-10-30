// no <string.h>: with macOS SDK headers memcpy is __builtin___memcpy_chk
void *memcpy(void *, const void *, __CPROVER_size_t);
void *memmove(void *, const void *, __CPROVER_size_t);

int main()
{
  char buffer[4];
  // the Microsoft runtime accepts a null pointer with a zero length; the
  // MSVC STL copies an empty vector with memcpy(dest, nullptr, 0)
  memcpy(buffer, 0, 0);
  memmove(buffer, 0, 0);
  __CPROVER_assert(buffer == buffer, "after the copies");
  // a non-zero length still needs a readable source
  char *nothing = 0;
  memcpy(buffer, nothing, 1);
  return 0;
}
