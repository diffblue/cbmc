// C++17 fold expressions (used by libc++ in C++11 mode)
template <class T>
struct is_arithmetic
{
  static const bool value = true;
};

template <class... Args>
struct S
{
  static_assert((is_arithmetic<Args>::value && ...));
};

int main()
{
  return 0;
}
