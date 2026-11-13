// Test that sizeof correctly handles C++ structs with typedef members,
// static members, and methods. These should not contribute to the
// struct size.
template <class T, T v>
struct integral_constant
{
  static constexpr T value = v;
  typedef T value_type;
  typedef integral_constant<T, v> type;
  constexpr operator value_type() const
  {
    return value;
  }
};

typedef integral_constant<bool, true> true_type;
typedef integral_constant<bool, false> false_type;

int main()
{
  true_type t;
  false_type f;
  return 0;
}
