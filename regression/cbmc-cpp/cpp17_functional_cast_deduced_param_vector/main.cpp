#include <vector>
extern "C" void __CPROVER_assert(bool, const char *);
struct ranget
{
  int *begin() const;
  int *end() const;
  template <class C> operator C() const
  {
    return C(begin(), end());
  }
};
int sum(std::vector<int> v);
int main()
{
  ranget r;
  __CPROVER_assert(sum(r) == sum(r), "conversion op to vector resolves");
  return 0;
}
