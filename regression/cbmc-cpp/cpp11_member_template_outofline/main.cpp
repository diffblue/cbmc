// Minimal test: member function template defined out-of-class
template <typename T>
struct S
{
  T val;
  template <typename U>
  void set(U x);
};

template <typename T>
template <typename U>
void S<T>::set(U x)
{
  val = x;
}

int main()
{
  S<int> s;
  s.set(42);
  __CPROVER_assert(s.val == 42, "member template out-of-line");
}
