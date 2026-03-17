// Two function templates that differ only in SFINAE enable_if constraints
// should not cause a duplicate declaration error.
template <bool B, typename T = void>
struct enable_if
{
};

template <typename T>
struct enable_if<true, T>
{
  typedef T type;
};

template <typename T>
struct is_int
{
  static const bool value = false;
};

template <>
struct is_int<int>
{
  static const bool value = true;
};

struct S
{
  template <
    typename U = int,
    typename enable_if<is_int<U>::value, bool>::type = true>
  S()
  {
  }

  template <
    typename U = int,
    typename enable_if<!is_int<U>::value, bool>::type = false>
  explicit S()
  {
  }
};

int main()
{
  S s;
  return 0;
}
