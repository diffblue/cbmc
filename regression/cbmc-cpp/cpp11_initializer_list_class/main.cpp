// N5008 [dcl.init.list]/5: initializing a std::initializer_list<int> object
// from a braced-init-list synthesises a backing const int[N] array and makes
// the object refer to it, so size() and element access reflect the list.
#include <initializer_list>
extern "C" void __CPROVER_assert(int, const char *);
int main()
{
  std::initializer_list<int> il = {1, 2, 3};
  __CPROVER_assert(il.size() == 3, "initializer_list size");
  __CPROVER_assert(*il.begin() == 1, "initializer_list first element");
  __CPROVER_assert(il.size() == 99, "WRONG size (must FAIL)");
  return 0;
}
