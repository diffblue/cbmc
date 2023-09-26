
int main()
{
  int a[2];
  int i;
  i = 0;

#ifndef _WIN64
  if (i==0)
    a[0l] = 1;
  else
    a[1l] = 2;
#else
  if(i == 0)
    a[0ll] = 1;
  else
    a[1ll] = 2;
#endif

  __CPROVER_assert(a[0] == 1 || a[1] == 2, "a[0]==1 || a[1]==2");

  return 0;
}

