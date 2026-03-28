// std::string constructor from const char* requires GCC 11+ libstdc++
#if !defined(__GNUC__) || __GNUC__ >= 11
// Verify std::string basic operations
#  include <cassert>
#  include <string>

int main()
{
  std::string s = "hello";
  assert(s.size() == 5);
  return 0;
}

#else
int main()
{
}
#endif
