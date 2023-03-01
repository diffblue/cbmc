#ifndef __GNUC__
_Bool __builtin_sub_overflow();
#endif

int main(void)
{
  __CPROVER_size_t result;
  int x;
  __CPROVER_assert(
    !__builtin_sub_overflow(
      (__CPROVER_size_t)((char *)&x + 1), (__CPROVER_size_t)&x, &result),
    "cannot overflow");
}
