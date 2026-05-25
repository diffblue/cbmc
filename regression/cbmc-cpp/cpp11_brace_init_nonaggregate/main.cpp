// [dcl.init.list] p3: brace-init for non-aggregate class types
// calls constructors, not aggregate initialization.
struct Base
{
  int x;
};
struct Derived : Base
{
  Derived(Base b) : Base(b)
  {
  }
};
Base make_base()
{
  return {42};
}
Derived make_derived()
{
  return {make_base()};
}
int main()
{
  Derived d = make_derived();
}
