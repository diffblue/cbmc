// C++17 if constexpr with discarded branch containing ill-formed code
template <typename T>
struct is_pointer
{
  static constexpr bool value = false;
};

template <typename T>
struct is_pointer<T *>
{
  static constexpr bool value = true;
};

template <typename T>
int deref_or_val(T x)
{
  if constexpr(is_pointer<T>::value)
    return *x;
  else
    return x;
}

int main()
{
  int val = 42;
  __CPROVER_assert(deref_or_val(val) == 42, "value path");
  __CPROVER_assert(deref_or_val(&val) == 42, "pointer path");
  return 0;
}
