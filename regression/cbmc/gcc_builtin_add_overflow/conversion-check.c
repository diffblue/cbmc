#ifndef __GNUC__
_Bool __builtin_add_overflow();
#endif

int main()
{
  unsigned a, b, c;
  if(__builtin_add_overflow(a, b, &c))
    return 0;
}
