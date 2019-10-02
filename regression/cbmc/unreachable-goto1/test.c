int main(int argc, char **argv)
{
  if(argc == 1)
  {
    do
    {
      __CPROVER_assume(0);
    } while(argc < 2);
  }

  assert(0);
}
