// C++26 language features require GCC 12+
#if !defined(__GNUC__) || __GNUC__ >= 12
// C++26 pack indexing
template <typename... Ts>
using first_t = Ts...[0];
int main()
{
  first_t<int, double, char> x = 42;
  __CPROVER_assert(x == 42, "pack index");
  return 0;
}

#else
int main()
{
}
#endif
