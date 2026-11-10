#if !defined(_MSC_VER) && __has_include(<compare>)
#  include <compare>
int main()
{
  std::strong_ordering so = std::strong_ordering::less;
  __CPROVER_assert(so < 0, "less < 0");
  __CPROVER_assert(!(so == 0), "less != 0");
}

#else
int main()
{
}
#endif
