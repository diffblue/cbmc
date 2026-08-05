int a[2];
int i;

int g(void)
{
  a[0] = 1;
  return 0;
}

int main()
{
  int j = 10 / a[i++] + g();
  return 0;
}
