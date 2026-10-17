// std::make_tuple requires GCC 11+ (SFINAE in return type on older GCC)
#if !defined(__GNUC__) && !defined(_MSC_VER) || __GNUC__ >= 11
#  include <tuple>

int main()
{
  auto t = std::make_tuple(1, 2.0);
  __CPROVER_assert(std::get<0>(t) == 1, "get<0>");
}

#else
int main()
{
}
#endif
