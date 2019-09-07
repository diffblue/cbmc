int main(int argc, char **argv)
{
  if(argc == 1)
  {
    __CPROVER_assume(0);
    do
    {
    } while(1);
  }

  assert(0);
}
