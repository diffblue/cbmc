// C++20 aggregate initialization with base class
struct Base
{
  int x;
};
struct Derived : Base
{
  int y;
};
int main()
{
  Derived d{{10}, 20};
  __CPROVER_assert(d.x == 10, "base member");
  __CPROVER_assert(d.y == 20, "derived member");
  return 0;
}
