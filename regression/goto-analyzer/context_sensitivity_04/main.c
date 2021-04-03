int step(int x)
{
  if(x == 0)
  {
    __CPROVER_assert(x == 0, "assertion x == 0");
    return 0;
  }
  else
  {
    return step(x - 1);
  }
}

int main(int argc, char **argv)
{
  int orig = 20;
  int res = step(orig);

  __CPROVER_assert(res == 0, "assertion res == 0");

  return 0;
}
