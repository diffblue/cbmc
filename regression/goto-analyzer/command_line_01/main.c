int f00(int x)
{
  __CPROVER_assert(x != 0, "assertion x != 0");
  return 0;
}

int main(int argc, char **argv)
{
  int v = 0;
  v = f00(v);
  __CPROVER_assert(v != 0, "assertion v != 0");

  return 0;
}
