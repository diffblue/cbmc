
int main()
{
  int i=0, j=2;

  if(i < 50)
  {
    i++;
    j++;
  }
  __CPROVER_assert(j != 3, "j!=3");
}
