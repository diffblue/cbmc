int x;
int *p;

int main()
{
  p = &x;
  x = 1;
#ifdef __GNUC__
  asm volatile("cli" ::: "memory");
#else
  __asm { cli }
#endif
  int out = *p;
  return out;
}
