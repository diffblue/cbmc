// GCC statement attributes -- currently "fallthrough" is the only one that GCC
// supports.
// https://gcc.gnu.org/onlinedocs/gcc/Statement-Attributes.html

int main()
{
  int x;
  switch(x)
  {
  case 1:
    x = 2;
#ifdef __GNUC__
    __attribute__((fallthrough));
#endif
  case 2:
  {
    x = 3;
#ifdef __GNUC__
    __attribute__((__fallthrough__));
#endif
  }
  case 3:
    break;
  }

  return 0;
}
