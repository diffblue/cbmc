int g=0;

int f()
{
  assert(g==0);
  g++;
}

int main()
{
l:
l2:;
  int i=f();
  goto l;
}
