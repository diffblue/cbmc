int main(int argc, char **argv)
{
  // A function containing 3 SESE regions: one delimiting the outer
  // if-block, and one delimiting the for-loop, despite a continue edge,
  // and another delimiting the conditional within the loop (which converges
  // before the bottom of the loop, to execute the loop increment).

  if(argc % 5)
  {
    for(int x = 0; x < 10; ++x)
    {
      if(x % 7)
        continue;
      ++x;
    }
  }
  else
  {
    --argc;
  }

  return argc;
}
