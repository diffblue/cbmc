
int main()
{
  int i=0, y;

  if (i==0)
    y=1;

  __CPROVER_assert(y == 0, "y==0");

  return 0;
}

