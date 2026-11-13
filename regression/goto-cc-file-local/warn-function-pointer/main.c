extern int target(int);
int kernel_entry(void);
int main(void)
{
  int (*fp)(int) = target;
  return fp(1) + kernel_entry();
}
