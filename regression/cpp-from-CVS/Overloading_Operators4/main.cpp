struct X
{
  X():i(1), j(2)
  {
  }

  int i;
  int j;
  
  bool operator == (const struct X &o)
  {
    return i==o.i &&
           j==o.j;
  }

  bool func()
  {
	  X x1, x2;
	  x1.i = 2;
	  return x1 == x2;
  }
};

void doit()
{
  X a, b;

  assert(a==b);
}

int main()
{
  doit();
  assert(!X().func());
}
