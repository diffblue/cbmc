int main(int argc, char **argv)
{
  // A function containing 3 SESE regions: one delimiting the outer
  // if-block, and one delimiting each for-loop.

  if(argc % 5)
  {
    for(int x = 0; x < 10; ++x)
    {
      for(int y = 0; y < 2; ++y)
      {
        ++x;
      }
    }
  }
  else
  {
    --argc;
  }

  return argc;
}
