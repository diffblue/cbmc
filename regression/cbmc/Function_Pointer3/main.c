
int nondet_int();
void assert(_Bool b);


typedef int (*FuncType)(int, int);

int f1(int a, int b)
{
  return a+b+1;
}

int f2(int x, int y)
{
  return x-y+2;
}

int main()
{
  int res;
  FuncType pf;

  if( nondet_int() )
    pf = f1;
  else
    pf = f2;

  res = pf(4,3);

  assert(res < 10);

  return res;
}
