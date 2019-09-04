int main(int argc, char **argv)
{
  // A function containing 2 SESE regions: one delimiting the outer
  // if-block, and one delimiting the do-while loop.

  if(argc % 5)
  {
    int x = 0;
    do
    {
      ++x;
    } while(x < 10);
  }
  else
  {
    --argc;
  }

  return argc;
}
