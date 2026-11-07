// std::unordered_set<int> with libstdc++ 16: after insert(42), size() == 1
// and count(42) == 1 do not hold (silent wrong result; no front-end
// diagnostic).  The same program verifies with gcc 13's headers.
#include <unordered_set>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::unordered_set<int> s;
  s.insert(42);
  __CPROVER_assert(s.size() == 1 && s.count(42) == 1, "unordered_set insert");
  return 0;
}
