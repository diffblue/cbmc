// Requires GCC 13+ or Clang (older libstdc++ lacks support).
#if !defined(__GNUC__) || defined(__clang__) ||                                \
  (__GNUC__ >= 13 && __GNUC__ <= 15)
// C++20: <format> header parsing
#  include <format>
int main()
{
}
#else
int main()
{
}
#endif
