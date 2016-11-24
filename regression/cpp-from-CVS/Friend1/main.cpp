class C
{
public:
  C(int _base):base(_base) { }

  typedef int T;

  friend int f()
  {
    T x=1;
    return x;
  }
  
  int base;
};

int main()
{
  C c(1);

  assert(f()==1);  
}
