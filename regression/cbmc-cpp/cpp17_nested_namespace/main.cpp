// C++17 nested namespace
namespace A::B::C
{
int value = 42;
}
int main()
{
  __CPROVER_assert(A::B::C::value == 42, "nested ns");
  return 0;
}
