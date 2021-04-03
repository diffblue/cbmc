int negate(int x)
{
  return -x;
}

int main(int argc, char **argv)
{
  int x = 23;
  int nx = negate(x);
  int nnx = negate(nx);

  __CPROVER_assert(x == nnx, "assertion x == nnx");

  return 0;
}
