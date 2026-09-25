// Test that a template class with overloaded methods can be instantiated
// without duplicate symbol errors when different overloads produce the
// same mangled name.
template <typename T>
struct S
{
  typedef T *pointer;
  typedef const T *const_pointer;

  void f(pointer p)
  {
  }
  void f(const_pointer p)
  {
  }
};

int main()
{
  S<const int> s;
  const int *p = 0;
  s.f(p);
  return 0;
}
