// Test SFINAE with default template arguments.
// When a default template argument fails to instantiate, the function
// template should be silently removed from the overload set.

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
struct is_pointer
{
  static const bool value = false;
};

template <typename T>
struct is_pointer<T *>
{
  static const bool value = true;
};

// This function template uses SFINAE via a default template argument.
// When T is not a pointer, enable_if<false>::type doesn't exist,
// so this overload should be silently discarded.
template <typename T, typename = typename enable_if<is_pointer<T>::value>::type>
void process(T t)
{
}

// Fallback overload for non-pointer types.
void process(int x)
{
}

int main()
{
  process(42); // Should call process(int), not the template
  int *p = 0;
  process(p); // Should call the template version
  return 0;
}
