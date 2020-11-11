
int main()
{
  int i;

  if(i>0)
    if(i<3)
      __CPROVER_assert(i >= 1 && i <= 2, "i>=1 && i<=2");

  return 0;
}
