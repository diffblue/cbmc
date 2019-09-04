int main(int argc, char **argv)
{
  // Function containing two SESE regions,
  // one per if-block.
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
    ++argc;
  }

  return argc;
}
