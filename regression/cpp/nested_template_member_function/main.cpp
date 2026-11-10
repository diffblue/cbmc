// Test out-of-class definition of member function templates
// (nested template declarations like template<T> template<U>).

template <typename T>
struct S
{
  template <typename U>
  void f(U x);

  void g(T x);
};

template <typename T>
template <typename U>
void S<T>::f(U x)
{
}

template <typename T>
void S<T>::g(T x)
{
}

int main()
{
  S<int> s1;
  S<char> s2;
  return 0;
}
