// Test that template aliases inside class templates can be resolved
// when accessed via :: in template context.
template <bool B>
struct bool_constant
{
  static const bool value = B;
};

template <typename T>
struct traits
{
  template <typename U>
  using check = bool_constant<true>;

  static bool test()
  {
    return check<T>::value;
  }
};

int main()
{
  bool b = traits<int>::test();
  (void)b;
}
