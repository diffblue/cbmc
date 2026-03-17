// std::initializer_list<T> as actual class with size()
#include <initializer_list>
int main()
{
  std::initializer_list<int> il = {1, 2, 3};
  __CPROVER_assert(il.size() == 3, "initializer_list size");
}
