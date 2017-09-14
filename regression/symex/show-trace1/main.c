int input();

int main()
{
  int i, j, k;

  i=input(); // expect 2
  j=input(); // expect 3
  k=input(); // expect 6

  if(i==2)
    if(j==i+1)
      if(k==i*j)
        __CPROVER_assert(0, "");
}
