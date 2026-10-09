// Partial specialization must distinguish cv-qualifiers
template <class T>
struct is_const
{
  static const bool value = false;
};

template <class T>
struct is_const<const T>
{
  static const bool value = true;
};

static_assert(!is_const<int>::value, "int is not const");
static_assert(is_const<const int>::value, "const int is const");

int main()
{
  return 0;
}
