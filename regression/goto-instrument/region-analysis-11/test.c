int main(int argc, char **argv)
{
  // A function containing 2 SESE regions, one for the outer if-block
  // and one for the while-loop, despite a break edge

  if(argc % 5)
  {
    int x = 0;
    while(x < 10)
    {
      if(x % 7)
        break;
      ++x;
    }
  }
  else
  {
    --argc;
  }

  return argc;
}
