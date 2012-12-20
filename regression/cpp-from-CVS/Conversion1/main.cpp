class T
{
public:
  T():x(0)
  {
  }

  T(int i, int j):x(i)
  {
  }
  
  int x;
};

int main()
{
  // alternate forms of conversion
  assert(unsigned(-1)==(unsigned)-1);

  assert(bool(10));
  
  T t=T(2, 3);
  assert(t.x==2);
}
