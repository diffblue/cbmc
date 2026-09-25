// Test that out-of-line methods of partial specializations are not
// applied when instantiating the primary template.
template <typename T, typename U>
struct S
{
  void f();
};

template <typename U>
struct S<bool, U>
{
  void f();
};

// Out-of-line method of primary template
template <typename T, typename U>
void S<T, U>::f()
{
}

// Out-of-line method of partial specialization
template <typename U>
void S<bool, U>::f()
{
}

int main()
{
  S<int, int> s;
  s.f();
}
