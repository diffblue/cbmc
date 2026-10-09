// <regex> crashes on GCC 9 (segfault during type-checking)
#if !defined(__GNUC__) && !defined(_MSC_VER) || __GNUC__ >= 11
// C++11 <regex> header parses and type-checks
#  include <regex>

int main()
{
  return 0;
}

#else
int main()
{
}
#endif
