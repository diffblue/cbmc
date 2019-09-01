int main(int argc, char **argv)
{
  // A function containing 2 SESE regions, one for the outer if-block
  // and one for the while-loop, despite a continue edge that branches
  // directly to the top of the loop.

  if(argc % 5)
  {
    int x = 0;
  top_continue:
    while(x < 10)
    {
      if(x % 7)
      {
        ++x;
        goto top_continue;
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
