// C++23 language features require GCC 11+
#if !defined(__GNUC__) && !defined(_MSC_VER) || __GNUC__ >= 11
// C++23 size_t literal suffix
int main()
{
  auto x = 42uz;
  __CPROVER_assert(x == 42, "size_t literal");
}

#else
int main()
{
}
#endif
