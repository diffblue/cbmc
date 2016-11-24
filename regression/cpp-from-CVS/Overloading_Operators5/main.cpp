int g;

struct X
{
  X()
  {
  }

  int i;
  int j;
  
  X &operator= (const struct X &r);
};

X &X::operator= (const struct X &r)
{
  g=2;
  return *this;
}

void doit()
{
  X a, b;

  g=1;
  
  a=b;
  
  assert(g==2);
}

int main()
{
  doit();
}
