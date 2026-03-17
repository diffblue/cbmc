template <typename T>
struct S
{
  T x;
  ~S();
};

template <typename T>
S<T>::~S()
{
  x = T();
}

int main()
{
  S<int> s;
  s.x = 42;
  return 0;
}
