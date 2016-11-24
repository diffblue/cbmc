class A
{
public:

  class B
  {
  public:
    typedef int tt;
  };
  
  class C
  {
  public:
    B::tt i;
  };
};

int main()
{
  A::C x;
  x.i=1;
}
