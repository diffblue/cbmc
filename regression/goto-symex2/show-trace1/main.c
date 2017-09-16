int input();

int main()
{
  int i, j, k;

  i=input();
  j=input();
  k=input();

  if(i==2)
    if(j==i+1)
      if(k==i*j)
        assert(0);
}
