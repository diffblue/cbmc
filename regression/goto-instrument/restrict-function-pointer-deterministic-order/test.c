typedef int (*fptr_t)(int);

int alpha(int x)
{
  return x + 1;
}

int beta(int x)
{
  return x + 2;
}

int gamma(int x)
{
  return x + 3;
}

int main(void)
{
  fptr_t fp;
  return fp(0);
}
