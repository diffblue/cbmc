
int main()
{
  int a[2]={0,0};

  if (a[0]==0)
    a[0]=1;

  __CPROVER_assert(a[0] == 1 /*|| a[0]==2*/, "a[0]==1 /*|| a[0]==2*/");

  return 0;
}

