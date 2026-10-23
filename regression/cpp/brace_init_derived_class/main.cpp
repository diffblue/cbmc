// Empty braced-init-list {} should value-initialize a class type,
// including classes with base classes.

struct base
{
  int x;
};
struct derived : public base
{
};

void foo(derived d)
{
}

int main()
{
  derived d1{};
  derived d2 = derived{};
  foo(derived{});
  return 0;
}
