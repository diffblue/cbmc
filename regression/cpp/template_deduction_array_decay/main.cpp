// Test that array types decay to pointer types during function template
// argument deduction, matching standard C++ behavior.
template <typename T1, typename T2>
bool my_equal(T1 first1, T1 last1, T2 first2)
{
  return true;
}

int main()
{
  int a[10];
  int *p = a + 10;
  int b[10];
  // a is int[10], p is int*, b is int[10]
  // T1 should be deduced as int* (array decays to pointer)
  // T2 should be deduced as int*
  my_equal(a, p, b);
}
