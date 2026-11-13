// A derived class's constructor must be able to access the base-class
// constructor used to initialize the base subobject ([class.base.init],
// [class.access.base]).  Here the base's default constructor is private
// and the derived constructor initializes the base implicitly (no
// mem-initializer names it), so the program is ill-formed and must be
// rejected -- not silently accepted as if the implicit base
// initialization bypassed access control.

struct base
{
private:
  base()
  {
  }
};

struct derived : base
{
  derived()
  {
  }
};

int main()
{
  derived d;
  return 0;
}
