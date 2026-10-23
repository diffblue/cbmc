// C++11 type aliases
template <typename T>
using Ptr = T *;
int main()
{
  int x = 42;
  Ptr<int> p = &x;
  __CPROVER_assert(*p == 42, "type alias");
  return 0;
}
