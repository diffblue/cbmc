int fun(int *a)
{
  if(!a)
  {
    return 0;
  }
  if(*a == 4)
  {
    return 1;
  }
  return 2;
}
