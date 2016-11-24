char a[100];

void f(const signed char x[])
{
  assert(x[0]==0);
}

int main()
{
  f(a);
}
