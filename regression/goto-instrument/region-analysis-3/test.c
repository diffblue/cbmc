int main(int argc, char **argv)
{
  // Function containing two SESE regions: the inner if-block and the whole
  // function. The outer if-block is specifically *not* a region due to
  // a spoiling outgoing edge,
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
    return argc - 1;
  }

  return argc;
}
