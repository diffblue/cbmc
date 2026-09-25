// Address-of a function call returning a reference in a member initializer.

struct A
{
};
const A &get_a();

struct B
{
  const A *p;
  B() : p(&get_a())
  {
  }
};

int main()
{
  B b;
  return 0;
}
