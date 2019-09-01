int main(int argc, char **argv)
{
  // Function containing two SESE regions: the inner if-block and the whole
  // function. The outer if-block is specifically *not* a region due to
  // a spoiling incoming edge.
  if(argc % 7)
    goto target;

  if(argc % 5)
  {
    if(argc % 2)
    {
      ++argc;
    }
    else
    {
      --argc;
    }
  }
  else
  {
  target:
    ++argc;
  }

  return argc;
}
