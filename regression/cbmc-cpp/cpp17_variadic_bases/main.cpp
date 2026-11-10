// C++17 class template with multiple bases
template <typename... Bases>
struct Overloaded : Bases...
{
};
struct A
{
  int get()
  {
    return 1;
  }
};
struct B
{
  int value()
  {
    return 2;
  }
};
int main()
{
  Overloaded<A, B> o;
  __CPROVER_assert(o.get() == 1, "base A");
  __CPROVER_assert(o.value() == 2, "base B");
  return 0;
}
