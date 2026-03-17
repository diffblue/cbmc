// GCC built-in type transformations: __remove_cv, __remove_reference,
// __remove_cvref.

template <typename T>
struct remove_cv
{
  using type = __remove_cv(T);
};

template <typename T>
struct remove_ref
{
  using type = __remove_reference(T);
};

template <typename T>
struct remove_cvref
{
  using type = __remove_cvref(T);
};

remove_cv<const volatile int>::type a = 1;
remove_ref<int &>::type b = 2;
remove_ref<int &&>::type c = 3;
remove_cvref<const int &>::type d = 4;

int main()
{
  return 0;
}
