// The CPROVER library gives __builtin_X the model of X, except for models
// taking a va_list: on aarch64 va_list is a struct, the declaration of
// __builtin_vsnprintf and the model of vsnprintf disagreed, and the
// model's va_list typedef was left dangling
extern "C" void __CPROVER_assert(bool, const char *);
int format(char *buffer, const char *fmt, ...)
{
  __builtin_va_list ap;
  __builtin_va_start(ap, fmt);
  int r = __builtin_vsnprintf(buffer, 4, fmt, ap);
  __builtin_va_end(ap);
  return r;
}
int main()
{
  char buffer[4];
  int r = format(buffer, "%d", 7);
  __CPROVER_assert(r == r, "returns");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
