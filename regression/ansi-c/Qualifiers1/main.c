int f(const int farg[const 5])
{
}

int g(const int * const garg)
{
  f(garg);
}

int main()
{
  int a;
  volatile int * const p=(int * const)&a;
  *((int * const)&a) = 1;
  *p=2;
  
  f(&a);
  g(&a);
}
