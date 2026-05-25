struct Base
{
  virtual int value() const
  {
    return 1;
  }
  virtual ~Base()
  {
  }
};

struct Derived : Base
{
  int value() const override
  {
    return 2;
  }
};

int main()
{
  Derived d;
  Base &b = d;
  int r = b.value();
  return r;
}
