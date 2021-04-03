int main(int argc, char *argv[])
{
  int y = 1;
  int z;
  if(y)
  {
    __CPROVER_assert(y != 0, "assertion y != 0");
    z = 1;
  }
  else
  {
    __CPROVER_assert(y == 0, "assertion y == 0");
    z = 0;
  }
  __CPROVER_assert(z == 1, "assertion z == 1");
}
