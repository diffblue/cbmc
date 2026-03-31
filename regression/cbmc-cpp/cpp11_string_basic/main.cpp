// std::string constructor from const char* requires GCC 11+ libstdc++
#if !defined(__GNUC__) && !defined(_MSC_VER) || __GNUC__ >= 11
// C++11 std::string basic usage
#  include <string>

int main()
{
  std::string s = "hello";
  __CPROVER_assert(s.size() == 5, "string size");
  return 0;
}

#else
int main()
{
}
#endif
