// std::string constructor from const char* requires GCC 11+ libstdc++
#if !defined(__GNUC__) || __GNUC__ >= 11
#  include <string>
int main()
{
  std::string s = "hello";
  __CPROVER_assert(s.size() == 5, "size");
}

#else
int main()
{
}
#endif
