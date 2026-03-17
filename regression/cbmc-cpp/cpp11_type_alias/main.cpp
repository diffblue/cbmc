// C++11 type alias and alias template
using IntPtr = int *;
template <typename T>
using Ptr = T *;
int main()
{
  int x = 42;
  IntPtr p = &x;
  Ptr<int> q = &x;
  __CPROVER_assert(*p == 42, "type alias");
  __CPROVER_assert(*q == 42, "alias template");
  return 0;
}
