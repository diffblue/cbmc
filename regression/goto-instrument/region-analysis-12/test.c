int main(int argc, char **argv)
{
  // A function containing 3 SESE regions, one for the outer if-block
  // and one for the while-loop, despite a continue edge, and one for
  // the conditional inside the loop.

  if(argc % 5)
  {
    int x = 0;
    while(x < 10)
    {
      if(x % 7)
      {
        ++x;
        continue;
      }
      ++x;
    }
  }
  else
  {
    --argc;
  }

  return argc;
}
