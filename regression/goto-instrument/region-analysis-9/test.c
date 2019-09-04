int main(int argc, char **argv)
{
  // A function containing 2 SESE regions: one delimiting the outer
  // if-block, and one delimiting the for-loop. The inner loop isn't
  // a region due to the edge that breaks directly out of both loops.

  if(argc % 5)
  {
    for(int x = 0; x < 10; ++x)
    {
      for(int y = 0; y < 2; ++y)
      {
        ++x;
        if(y == 1)
          goto doublebreak;
      }
    }
  doublebreak:
    ++argc;
  }
  else
  {
    --argc;
  }

  return argc;
}
