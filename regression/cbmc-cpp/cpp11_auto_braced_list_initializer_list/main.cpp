#include <initializer_list>
#include <type_traits>

extern "C" void __CPROVER_assert(bool, const char *);

// [dcl.type.auto.deduct]/4: copy-list-initialization of a placeholder deduces
// std::initializer_list<U>, U deduced from each element as for a call
auto global_list = {10, 20};

template <class T>
int sum(T a, T b)
{
  auto il = {a, b};
  int s = 0;
  for(auto x : il)
    s += x;
  return s + static_cast<int>(il.size());
}

int main()
{
  auto il = {1, 2, 3};
  static_assert(
    std::is_same<decltype(il), std::initializer_list<int>>::value,
    "auto deduces std::initializer_list<int>");
  __CPROVER_assert(
    sizeof(il) == sizeof(std::initializer_list<int>) && il.size() == 3 &&
      il.begin()[2] == 3,
    "auto deduces std::initializer_list");

  // [temp.deduct.call]/2: an array element decays; `const' qualifies the
  // deduced std::initializer_list
  const auto strings = {"a", "bc"};
  static_assert(
    std::is_same<decltype(strings), const std::initializer_list<const char *>>::
      value,
    "const auto deduces const std::initializer_list<const char *>");
  __CPROVER_assert(strings.begin()[1][1] == 'c', "elements decay");

  __CPROVER_assert(
    global_list.size() == 2 && global_list.begin()[1] == 20, "namespace scope");
  __CPROVER_assert(sum(3, 4) == 9, "in a template");

  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
