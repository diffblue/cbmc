// C++23 language features require GCC 11+
#if !defined(__GNUC__) || __GNUC__ >= 11
// C++23 size_t literal suffix
int main()
{
  auto x = 42uz;
  __CPROVER_assert(x == 42, "42uz==42");
  return 0;
}

#else
int main()
{
}
#endif
