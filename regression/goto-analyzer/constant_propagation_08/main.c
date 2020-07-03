
int main()
{
  int a[2];
  int i;
  i = 0;

  if (i==0)
    a[0]=1;
  else
    a[1]=2;

  __CPROVER_assert(a[0] == 1 || a[1] == 2, "a[0]==1 || a[1]==2");

  return 0;
}

