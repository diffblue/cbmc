// Template argument deduction for const T* should deduce T from
// a const pointer argument, stripping the const qualifier.
template <typename C>
struct S
{
  C x;
  S() : x()
  {
  }
};

template <typename C>
S<C> operator+(const C *a, const S<C> &b)
{
  return b;
}

int main()
{
  S<char> s;
  const char *p = "x";
  S<char> r = p + s;
  return 0;
}
