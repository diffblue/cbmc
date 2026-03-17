// Partial specialization must preserve const in pointer base types.
// less<const A*> should match less<T*> with T = const A.

template <typename T>
struct less
{
  bool operator()(const T &a, const T &b) const
  {
    return false;
  }
};

template <typename T>
struct less<T *>
{
  bool operator()(T *a, T *b) const
  {
    return false;
  }
};

struct A
{
};

// Function template deduction should strip top-level const.
// f(const int) called with const int should deduce T = int.
template <typename T>
T identity(T x)
{
  return x;
}

int main()
{
  // Partial specialization: T should be const A
  less<const A *> l;
  const A *p1 = 0;
  const A *p2 = 0;
  l(p1, p2);

  // Function template: top-level const stripped
  const int ci = 42;
  int r = identity(ci);

  return 0;
}
