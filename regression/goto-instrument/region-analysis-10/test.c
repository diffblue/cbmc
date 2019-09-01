int main(int argc, char **argv)
{
  // A function containing 2 SESE regions: one delimiting the outer
  // if-block, and one delimiting the while-loop.

  if(argc % 5)
  {
    int x = 0;
    while(x < 10)
    {
      ++x;
    }
  }
  else
  {
    --argc;
  }

  return argc;
}
