// 0.0 is not a null pointer constant (C11 6.3.2.3p3), so a pointer cannot be
// compared with it either.
int g(int *p)
{
  return p != 0.0;
}

int main(void)
{
  return 0;
}
