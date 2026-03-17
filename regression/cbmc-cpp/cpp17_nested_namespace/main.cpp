// C++17 nested namespace definition
namespace A::B::C
{
int value = 42;
}
int main()
{
  __CPROVER_assert(A::B::C::value == 42, "nested namespace");
  return 0;
}
