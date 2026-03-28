int main()
{
  int x = 5;
  if(x < 0)
  {
    // This code is unreachable because x = 5 > 0
    int y = x + 1;
  }
  return 0;
}
