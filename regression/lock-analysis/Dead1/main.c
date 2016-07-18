int main()
{
  int y;

  {
  int *x=&y;

  }
  
  assert(y>=0);
}
