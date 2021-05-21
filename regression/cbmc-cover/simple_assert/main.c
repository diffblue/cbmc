int main(int argc, char *argv[])
{
  int x = 5;
  __CPROVER_assert(x == 5, "assertion x == 5");

  return 0;
}
