// Template argument deduction should fail when the same parameter
// is deduced to different types from different arguments.
template <typename T>
T add(T a, T b)
{
  return a + b;
}

int add(int a, int b)
{
  return a + b;
}

int main()
{
  // T cannot be deduced consistently (unsigned long vs char),
  // so the non-template overload should be selected.
  int r = add((unsigned long)1, (char)2);
  return r;
}
