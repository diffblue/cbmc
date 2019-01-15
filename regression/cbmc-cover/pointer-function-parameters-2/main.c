int fun(int **a)
{
  if(!a)
  {
    return 0;
  }
  if(!*a)
  {
    return 1;
  }
  if(**a==4)
  {
    return 2;
  }
  return 3;
}
