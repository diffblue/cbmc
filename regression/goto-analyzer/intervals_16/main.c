
int main()
{
  int i=0, j=2;

  while(i <= 50)
  {
    i++;
    j++;
  }
  __CPROVER_assert(j < 52, "j<52");
}

