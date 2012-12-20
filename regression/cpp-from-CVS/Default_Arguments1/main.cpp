//#include <assert.h>

int f(int d=1)
{
  return d;
}

int g(int x, int d=1, int q=2)
{
  return d;
}

int global;

int h(int &r=global)
{
  return r;
}

void doit()
{
  assert(f()==1);
  assert(f(2)==2);
  assert(g(0)==1);
  assert(g(1, 2)==2);

  global=10;
  assert(h()==10);
}

int main()
{
  doit();
}

