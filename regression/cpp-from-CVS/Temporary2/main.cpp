class X
{
public:
  X()
  {
  }

  X(int i):z(i)
  {
  }
  
  int z;
};

void doit()
{
  X x;

  x=X(1);
}

int main()
{
  doit();
}
