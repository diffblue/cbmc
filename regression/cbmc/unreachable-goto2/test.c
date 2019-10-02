int main(int argc, char **argv)
{
  if(argc == 1)
  {
    while(argc < 2)
    {
      __CPROVER_assume(0);
    }
  }

  assert(0);
}
