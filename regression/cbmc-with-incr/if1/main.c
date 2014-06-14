int main()
{
  int i, j;

  i = 1;

  if(j > 0)
    j += i;
  else
    j = 0;

  assert(i != j);
}
