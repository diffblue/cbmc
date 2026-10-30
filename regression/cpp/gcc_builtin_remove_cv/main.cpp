// __remove_cv, __remove_reference, __remove_cvref are GCC 13+ / Clang builtins.
// On older GCC these identifiers are used as struct/alias names in libstdc++.
#if(defined(__GNUC__) && !defined(__clang__) && __GNUC__ >= 13) ||             \
  defined(__clang__)

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

#endif

int main()
{
  return 0;
}
