class C
{
public:
  C(int _base):base(_base) { }

  int operator [] (int x)
  {
    return base+x;
  }
  
  int operator [] (class Z &z)
  {
    return 0;
  }
  
  int base;
};

int main()
{
  C c(1);
  
  assert(c[0]==1);
  assert(c[2]==3);
}
