int x;
int y;
int *p = &x;
int *q;

int main()
{
  int *local_p = &y;
#ifdef __GNUC__
  asm volatile("cli" ::: "memory");
#else
  __asm { cli }
#endif
  int *r = q;
  return 0;
}
