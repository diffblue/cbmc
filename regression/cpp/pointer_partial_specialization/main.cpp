// Test that pointer partial specializations are correctly matched.
// This pattern is used by std::iterator_traits<T*>.

template <typename T>
struct traits
{
};

template <typename T>
struct traits<T *>
{
  typedef int category;
};

int main()
{
  traits<char *>::category c = 42;
  return c;
}
