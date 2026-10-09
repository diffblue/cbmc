struct Base
{
  int x;
};

struct Derived : Base
{
  Derived() : Base{42}
  {
  }
};

int main()
{
  Derived d;
  return 0;
}
