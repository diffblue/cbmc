extern "C" void __CPROVER_assert(bool, const char *);
#include <utility>
int sum() { return 0; }
template <class T> int sum(T t) { return t; }
template <class T, class U> int sum(T t, U u) { return t + u; }
struct Y
{
  int v;
  template <class... Args, class Result = int>
  Result operator()(Args &&...args) const { return v + sum(std::forward<Args>(args)...); }
};
int main()
{
  Y y{7};
  __CPROVER_assert(y() == 7, "empty pack expanded in body, trailing defaulted param");
  __CPROVER_assert(y(1, 2) == 10, "two-element pack");
  return 0;
}
