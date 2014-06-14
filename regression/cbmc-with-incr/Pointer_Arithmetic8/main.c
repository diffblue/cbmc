void f(int *);

int main()
{
  int a[5];

  f(a);
}

void f(int *p)
{
  p[10]=0;
}
