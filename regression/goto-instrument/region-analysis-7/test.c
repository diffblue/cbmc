int main(int argc, char **argv)
{
  // A function containing 1 SESE region delimiting the whole function, because
  // of a spoiling return edge defeating what would otherwise be regions.

  if(argc % 5)
  {
    for(int x = 0; x < 10; ++x)
    {
      if(x % 7)
        return;
      ++x;
    }
  }
  else
  {
    --argc;
  }

  return argc;
}
