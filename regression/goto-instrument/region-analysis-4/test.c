int main(int argc, char **argv)
{
  // A function containing 2 SESE regions: one delimiting the outer
  // if-block, and one delimiting the for-loop.

  if(argc % 5)
  {
    for(int x = 0; x < 10; ++x)
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
