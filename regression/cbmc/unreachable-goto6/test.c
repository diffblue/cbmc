int main(int argc, char **argv)
{
  if(argc > 1)
  {
    __CPROVER_assume(0);

    if(argc == 2)
    {
      ++argc;
    }
    else
    {
      --argc;
    }
  }

  assert(0);
}
