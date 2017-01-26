
extern int a;
extern void sub(void);

void func(void)
{
  int i, n=2;
  n = a ? n : n+1;  // n = 2 or 3
  for (i=0; i<n; i++)
    sub();
}

int main()
{
  func();
  return 0;
}

