// N5008 [dcl.init.list]/5: a braced-init-list argument for a parameter of
// type std::initializer_list<E> constructs the object from a backing array
// of E.  The front end found E from the initializer_list layout's pointer
// member by NAME -- libstdc++'s `_M_array', MSVC's `_begin' -- so with
// libc++ (`__begin_') no call with a braced-init-list argument resolved
// ("found no match for symbol 'count'"), in three places (conversion,
// viability, initializer-list-constructor detection).  Read the member by
// position instead ([support.initlist]: the first data member is the
// pointer to the first element in every implementation).
extern "C" void __CPROVER_assert(bool, const char *);
#include <initializer_list>

enum class E
{
  A,
  B,
  C
};
struct S
{
  int v;
};

int count(std::initializer_list<int> xs)
{
  return xs.size();
}
int count_e(std::initializer_list<E> xs)
{
  return xs.size();
}
int sum_s(std::initializer_list<S> xs)
{
  int s = 0;
  for(const S &x : xs)
    s += x.v;
  return s;
}
constexpr int csum(std::initializer_list<int> xs)
{
  int s = 0;
  for(int x : xs)
    s += x;
  return s;
}
static_assert(csum({1, 2, 3}) == 6, "constexpr over initializer_list");

int main()
{
  __CPROVER_assert(count({1, 2}) == 2 && count({}) == 0, "int list");
  __CPROVER_assert(count_e({E::A, E::B, E::C}) == 3, "enum list");
  __CPROVER_assert(sum_s({{1}, {2}, {3}}) == 6, "class list");
  __CPROVER_assert(count({1, 2}) == 3, "WRONG (must FAIL)");
}
