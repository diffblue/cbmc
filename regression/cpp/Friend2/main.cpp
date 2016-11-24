class X
{
private:
  int x;

  friend void f()
  {
    X aa;
    aa.x=1;
  }
  
public:
  X() { }
};

int main()
{
}
