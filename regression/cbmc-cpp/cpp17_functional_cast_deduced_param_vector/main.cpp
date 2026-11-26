#include <vector>
extern "C" void __CPROVER_assert(bool, const char *);
static int data[3] = {1, 2, 3};
struct ranget
{
  int *begin() const
  {
    return data;
  }
  int *end() const
  {
    return data + 3;
  }
  template <class C>
  operator C() const
  {
    return C(begin(), end());
  }
};
int sum(std::vector<int> v)
{
  int s = 0;
  for(std::size_t i = 0; i < v.size(); ++i)
    s += v[i];
  return s;
}
int main()
{
  ranget r;
  __CPROVER_assert(sum(r) == 6, "conversion op to vector resolves");
  return 0;
}
