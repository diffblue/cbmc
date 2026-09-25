// C++11 (DR 45): nested classes have access to the enclosing class's
// private and protected members.
class A
{
  int priv;

protected:
  int prot;

public:
  class B
  {
  public:
    int get_priv(const A &a)
    {
      return a.priv;
    }
    int get_prot(const A &a)
    {
      return a.prot;
    }
  };
};

int main()
{
  A a;
  A::B b;
  b.get_priv(a);
  b.get_prot(a);
  return 0;
}
