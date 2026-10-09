// libc++ uses __attribute__ before the namespace name and inline variables
namespace __attribute__((__type_visibility__("default"))) std
{
  inline namespace __1
  {
  template <class T, bool V>
  struct integral_constant
  {
    // C++17 inline variable (used by libc++ even in C++11 mode)
    static inline constexpr const bool value = V;
  };

  typedef integral_constant<bool, true> true_type;
  typedef integral_constant<bool, false> false_type;
  } // namespace __1
} // namespace std

int main()
{
  static_assert(std::true_type::value, "true_type is true");
  static_assert(!std::false_type::value, "false_type is false");
  return 0;
}
